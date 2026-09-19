package id.varino.danareceiver;

import android.accessibilityservice.AccessibilityService;
import android.accessibilityservice.AccessibilityServiceInfo;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.Intent;
import android.net.Uri;
import android.accessibilityservice.GestureDescription;
import android.graphics.Path;
import android.graphics.Bitmap;
import android.graphics.ColorSpace;
import android.os.Build;
import android.hardware.HardwareBuffer;
import android.view.Display;
import android.provider.Settings;
import android.text.TextUtils;
import android.util.Log;
import android.widget.Toast;
import android.os.Vibrator;
import android.os.VibrationEffect;
import android.view.accessibility.AccessibilityEvent;
import android.view.accessibility.AccessibilityNodeInfo;
import android.view.accessibility.AccessibilityWindowInfo;

import com.google.mlkit.vision.barcode.BarcodeScanner;
import com.google.mlkit.vision.barcode.BarcodeScannerOptions;
import com.google.mlkit.vision.barcode.BarcodeScanning;
import com.google.mlkit.vision.barcode.common.Barcode;
import com.google.mlkit.vision.common.InputImage;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;
import java.util.regex.Matcher;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * V26 10-POINT SELF-CALIBRATING ENVELOPE TAP + CLAIM-AMOUNT SUCCESS + 120s AUTO-CLOSE.
 *
 * Important design rule: never dispatch a tap while another app is in the
 * foreground. This prevents the receiver from stealing the user's screen.
 * The service may auto-click DANA UI only when the current accessible window
 * belongs to id.dana. A valid trigger is stored by NtfyService and consumed
 * when DANA is actually visible.
 */
public class DanaAutoClickAccessibilityService extends AccessibilityService {
    public static final String TAG = "DanaAutoClickV26";
    private static final String DANA_PACKAGE = "id.dana";
    private static final String TELEGRAM_PACKAGE = "org.telegram.messenger";
    private static final String TELEGRAM_BETA_PACKAGE = "org.telegram.messenger.beta";
    private static final long QR_SCAN_INTERVAL_MS = 1500L;
    private static final long QR_DEDUP_MS = 30000L;
    private static final String BUTTON_TEXT = "BUKA DANA";
    // DANA Kaget can render the envelope as a custom view with no clickable
    // Accessibility node. In that case we use a guarded coordinate fallback
    // only after the DANA screen itself is positively detected.
    private static final String ENVELOPE_HINT = "tap amplop";
    private static final String ENVELOPE_HINT_2 = "lihat dana kaget";
    private static final float[] ENVELOPE_TAP_XS = {
            0.50f, 0.46f, 0.54f, 0.50f, 0.46f,
            0.54f, 0.46f, 0.54f, 0.50f, 0.50f
    };
    private static final float[] ENVELOPE_TAP_YS = {
            0.445f, 0.445f, 0.445f, 0.405f, 0.405f,
            0.405f, 0.485f, 0.485f, 0.485f, 0.525f
    };
    private static final long TAP_VERIFY_DELAY_MS = 350L;
    private static final long DIRECT_TAP_START_DELAY_MS = 700L;
    private static final int DIRECT_TAP_MAX_ATTEMPTS = 10;
    private static final long DIRECT_TAP_ATTEMPT_GAP_MS = 650L;
    private static final long DIRECT_TAP_FALLBACK_AFTER_MS = 4000L;
    private static final long DANA_MAIN_READY_DELAY_MS = 650L;
    private static final long LAST_DANA_EVENT_FALLBACK_MS = 15000L;
    private static final String TRIGGER_TEXT = "DANA Kaget terdeteksi";
    private static final long RETRY_WINDOW_MS = 20000L;
    private static final long CLAIM_CONFIRM_WINDOW_MS = 15000L;
    // V26: once the DANA Kaget result page shows a real Rupiah amount,
    // the claim is considered successful immediately.
    private static final long DANA_MAX_OPEN_MS = 120000L;
    private static final long CLOSE_GESTURE_DURATION_MS = 90L;
    private static final Pattern RUPIAH_AMOUNT_PATTERN =
            Pattern.compile("(?i)\\brp\\s*[0-9][0-9\\.,]*\\b");
    private static final int RESULT_NOTIFICATION_ID = 2002;
    private static final String RESULT_CHANNEL = "dana_result";
    // V25 FIX: channel senyap khusus notifikasi status SEMENTARA (bukan hasil akhir),
    // supaya tidak ikut memicu heads-up/notification shade terbuka ulang selama
    // proses direct-tap masih berjalan (lihat showResultNotification()).
    private static final String RESULT_CHANNEL_QUIET = "dana_result_quiet";
    private static final String[] SUCCESS_TEXTS = {
            "dana kaget berhasil",
            "berhasil diklaim",
            "berhasil menerima",
            "kamu mendapatkan",
            "uang berhasil diterima",
            "dana kaget masuk"
    };
    private static final String[] FAILURE_TEXTS = {
            "dana kaget sudah habis",
            "dana kaget telah habis",
            "sudah diambil",
            "sudah diklaim",
            "gagal",
            "tidak berhasil",
            "kuota habis",
            "coba lagi"
    };

    private final android.os.Handler handler = new android.os.Handler(android.os.Looper.getMainLooper());
    private boolean armed = false;
    private long armedAt = 0L;
    private boolean clickInProgress = false;
    private boolean awaitingClaimResult = false;
    private boolean danaUiNotified = false;
    private long clickedAt = 0L;
    private int directTapAttempts = 0;
    private long directTapStartedAt = 0L;
    private int currentTapPointIndex = -1;
    private float currentTapNormalizedX = -1f;
    private float currentTapNormalizedY = -1f;
    private int learnedTapPointIndex = -1;
    private boolean directTapScheduled = false;
    private boolean directTapSequenceActive = false;
    // V25 FIX: hitungan retry KHUSUS saat tap ditunda karena package aktif bukan
    // DANA (notification shade/app lain sedang menutupi layar). Tidak memakan
    // jatah directTapAttempts, tapi tetap dibatasi supaya tidak retry selamanya
    // kalau DANA memang tidak kembali ke foreground.
    private int shadeWaitRetries = 0;
    private static final int MAX_SHADE_WAIT_RETRIES = 15;
    private static final long SHADE_WAIT_RETRY_DELAY_MS = 300L;
    private String lastEventPackage = "";
    private long lastEventAt = 0L;
    private long lastDanaEventAt = 0L;
    private String lastDanaEventClass = "";
    private long danaOpenAt = 0L;
    private boolean danaLoadingWaitLogged = false;
    private boolean danaFallbackScheduled = false;
    private boolean danaTimeoutScheduled = false;
    private long lastDebugSignalAt = 0L;
    private String lastTracePackage = "";
    private int lastTraceEventType = -1;
    private String lastTraceUiFingerprint = "";
    private long lastTraceUiAt = 0L;

    // V25: QR scanner for DANA Kaget images displayed in Telegram.
    // The scanner only accepts the official DANA Kaget URL format; other
    // QR codes (QRIS, Wi-Fi, contacts, etc.) are ignored.
    private final ExecutorService qrExecutor = Executors.newSingleThreadExecutor();
    private final BarcodeScanner qrScanner = BarcodeScanning.getClient(
            new BarcodeScannerOptions.Builder()
                    .setBarcodeFormats(Barcode.FORMAT_QR_CODE)
                    .build()
    );
    private volatile boolean qrScanInProgress = false;
    private long lastQrScanAt = 0L;
    private String lastQrUrl = "";
    private long lastQrDetectedAt = 0L;

    @Override
    protected void onServiceConnected() {
        super.onServiceConnected();
        AccessibilityServiceInfo info = getServiceInfo();
        if (info == null) info = new AccessibilityServiceInfo();
        info.eventTypes = AccessibilityEvent.TYPE_NOTIFICATION_STATE_CHANGED
                | AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED
                | AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED
                | AccessibilityEvent.TYPE_VIEW_CLICKED;
        info.feedbackType = AccessibilityServiceInfo.FEEDBACK_GENERIC;
        info.notificationTimeout = 50;
        info.flags = AccessibilityServiceInfo.FLAG_REPORT_VIEW_IDS
                | AccessibilityServiceInfo.FLAG_RETRIEVE_INTERACTIVE_WINDOWS;
        info.packageNames = null;
        setServiceInfo(info);
        armed = hasPendingClaim();
        clickInProgress = false;
        directTapAttempts = 0;
        directTapStartedAt = 0L;
        directTapScheduled = false;
        directTapSequenceActive = false;
        danaOpenAt = 0L;
        danaLoadingWaitLogged = false;
        danaFallbackScheduled = false;
        danaTimeoutScheduled = false;
        danaUiNotified = false;
        lastTracePackage = "";
        lastTraceEventType = -1;
        lastTraceUiFingerprint = "";
        lastTraceUiAt = 0L;
        Log.i(TAG, "V25 Accessibility aktif. Full debug trace + adaptive loading + 10x calibrated verified direct tap mode siap.");
        DebugTrace.step(this, "AccessibilityService aktif");
        DebugTrace.detail(this, "Config: DANA=" + DANA_PACKAGE + " | Telegram=" + TELEGRAM_PACKAGE + " | retry=" + RETRY_WINDOW_MS + "ms | confirm=" + CLAIM_CONFIRM_WINDOW_MS + "ms");
        if (armed) scheduleRetries();
    }

    @Override
    public void onAccessibilityEvent(AccessibilityEvent event) {
        if (event == null) return;

        String pkg = event.getPackageName() == null ? "" : event.getPackageName().toString();
        lastEventPackage = pkg;
        lastEventAt = System.currentTimeMillis();
        if (DANA_PACKAGE.equals(pkg)) {
            lastDanaEventAt = lastEventAt;
            lastDanaEventClass = event.getClassName() == null ? "" : event.getClassName().toString();
        }
        String text = eventText(event);
        traceAccessibilityEvent(event, pkg, text);

        // V25: when a Telegram screen changes, inspect the visible screen for
        // a QR code. This is screenshot-only; nothing is tapped in Telegram.
        // Only a QR whose decoded value is an official DANA Kaget URL can
        // trigger the DANA claim flow.
        if (isTelegramPackage(pkg)
                && event.getEventType() != AccessibilityEvent.TYPE_NOTIFICATION_STATE_CHANGED) {
            scheduleQrScreenScan();
        }

        if (DANA_PACKAGE.equals(pkg) && hasPendingClaim()) {
            long danaNow = System.currentTimeMillis();

            // A trigger can arrive while AccessibilityService is already running.
            // Arm the visit from the actual DANA event and NEVER depend on
            // onServiceConnected() being called again.
            if (!armed) {
                armed = true;
                armedAt = danaNow;
                currentTapPointIndex = -1;
                currentTapNormalizedX = -1f;
                currentTapNormalizedY = -1f;
            }
            if (danaOpenAt == 0L) {
                danaOpenAt = danaNow;
                danaLoadingWaitLogged = false;
                scheduleDanaTimeout();
                DebugTrace.detail(this, "DANA visit armed from Accessibility event; starting adaptive tap timer + 120s watchdog");
            }

            // V26: the DANA Kaget success screen is the authoritative signal.
            // Do this before any further tap scheduling so a visible Rupiah
            // amount immediately stops the remaining direct-tap sequence.
            if ((directTapSequenceActive || awaitingClaimResult)
                    && detectClaimAmountSuccess(eventText(event))) {
                claimConfirmed(true, eventText(event));
                return;
            }

            // Android/OEM notification shade can remain above DANA even though
            // Accessibility reports id.dana. Dismiss it before the direct tap.
            if (isDanaMainReadyClass(event.getClassName())) {
                DebugTrace.detail(this, "DANA main/Griver window detected; dismissing notification shade before fixed tap");
                dismissNotificationShadeSafely();
                if (!directTapScheduled && !directTapSequenceActive && !awaitingClaimResult) {
                    directTapScheduled = true;
                    handler.postDelayed(() -> {
                        directTapScheduled = false;
                        if (armed && hasPendingClaim() && !awaitingClaimResult && !directTapSequenceActive) {
                            DebugTrace.step(this, "DANA main ready -> fixed coordinate tap sequence");
                            startDirectTapSequence();
                        }
                    }, DANA_MAIN_READY_DELAY_MS);
                }
            }

            // Guaranteed fallback: if the expected class event is missing,
            // still attempt the fixed coordinate sequence after loading settles.
            if (!danaFallbackScheduled) {
                danaFallbackScheduled = true;
                DebugTrace.detail(this, "Scheduling guaranteed DANA fallback check in "
                        + DIRECT_TAP_FALLBACK_AFTER_MS + "ms");
                handler.postDelayed(() -> {
                    danaFallbackScheduled = false;
                    if (hasPendingClaim() && armed && !awaitingClaimResult && !directTapSequenceActive) {
                        DebugTrace.detail(this, "Guaranteed DANA fallback check fired");
                        dismissNotificationShadeSafely();
                        tryClickDanaButton();
                    }
                }, DIRECT_TAP_FALLBACK_AFTER_MS);
            }
        }

        if (DANA_PACKAGE.equals(pkg) && hasPendingClaim() && !danaUiNotified) {
            danaUiNotified = true;
            DebugTrace.success(this, "UI DANA terdeteksi");
            showResultNotification("📱 UI DANA terdeteksi. Receiver siap memproses DANA Kaget.", false);
            Log.i(TAG, "UI DANA terdeteksi untuk pending claim.");
        }

        if (DANA_PACKAGE.equals(pkg) && (directTapSequenceActive || awaitingClaimResult)) {
            if (detectClaimAmountSuccess(text)) {
                claimConfirmed(true, text);
                return;
            }
            String normalized = text == null ? "" : text.toLowerCase();
            if (awaitingClaimResult && containsAny(normalized, SUCCESS_TEXTS)) {
                claimConfirmed(true, text);
                return;
            }

            if (containsAny(normalized, FAILURE_TEXTS)) {
                claimConfirmed(false, text);
                return;
            }
            checkDanaRootForClaimResult();
            if (awaitingClaimResult && clickedAt > 0L && System.currentTimeMillis() - clickedAt > CLAIM_CONFIRM_WINDOW_MS) {
                claimNotConfirmed();
                return;
            }
        }

        if (event.getEventType() == AccessibilityEvent.TYPE_NOTIFICATION_STATE_CHANGED
                && getPackageName().equals(pkg)
                && (containsIgnoreCase(text, TRIGGER_TEXT) || containsIgnoreCase(text, BUTTON_TEXT))) {
            armed = hasPendingClaim();
            if (armed) {
                Log.i(TAG, "Trigger valid. Menunggu/menangani UI DANA tanpa mengganggu aplikasi lain.");
                scheduleRetries();
            }
            return;
        }

        if (hasPendingClaim()) armed = true;
        if (armed && DANA_PACKAGE.equals(pkg)) {
            tryClickDanaButton();
        }
    }

    private boolean isDanaMainReadyClass(CharSequence className) {
        if (className == null) return false;
        String c = className.toString();
        return c.contains("id.dana.home_v2.main.MainHomeActivity")
                || c.contains("com.alibaba.griver.core.ui.activity.GriverBaseActivity$Main");
    }

    private void dismissNotificationShadeSafely() {
        try {
            boolean ok = performGlobalAction(AccessibilityService.GLOBAL_ACTION_DISMISS_NOTIFICATION_SHADE);
            DebugTrace.detail(this, "Dismiss notification shade: " + ok);
        } catch (Exception e) {
            DebugTrace.detail(this, "Dismiss notification shade exception=" + e.getClass().getSimpleName());
        }
    }

    private void traceAccessibilityEvent(AccessibilityEvent event, String pkg, String text) {
        int type = event.getEventType();
        long now = System.currentTimeMillis();
        boolean packageChanged = !pkg.equals(lastTracePackage);
        boolean typeChanged = type != lastTraceEventType;
        if (packageChanged || typeChanged) {
            String cls = event.getClassName() == null ? "" : event.getClassName().toString();
            DebugTrace.detail(this, "AccessibilityEvent type=" + accessibilityEventName(type)
                    + " pkg=" + (pkg.isEmpty() ? "(none)" : pkg)
                    + " class=" + shortValue(cls, 100)
                    + " text=" + shortValue(text, 180));
            lastTracePackage = pkg;
            lastTraceEventType = type;
        } else if (DANA_PACKAGE.equals(pkg) && now - lastTraceUiAt >= 1200L) {
            String ui = text == null ? "" : text.trim();
            String fp = ui.length() > 220 ? ui.substring(0, 220) : ui;
            if (!fp.equals(lastTraceUiFingerprint)) {
                DebugTrace.detail(this, "DANA UI changed: text=" + shortValue(ui, 260));
                lastTraceUiFingerprint = fp;
                lastTraceUiAt = now;
            }
        }
        // V26: do not log the source-id for every accessibility event.
        // High-frequency source-id logging was one of the avoidable CPU/log costs.
    }

    private String accessibilityEventName(int type) {
        switch (type) {
            case AccessibilityEvent.TYPE_NOTIFICATION_STATE_CHANGED: return "NOTIFICATION_STATE_CHANGED";
            case AccessibilityEvent.TYPE_WINDOW_STATE_CHANGED: return "WINDOW_STATE_CHANGED";
            case AccessibilityEvent.TYPE_WINDOW_CONTENT_CHANGED: return "WINDOW_CONTENT_CHANGED";
            case AccessibilityEvent.TYPE_VIEW_CLICKED: return "VIEW_CLICKED";
            default: return "TYPE_" + type;
        }
    }

    private String shortValue(String value, int max) {
        if (value == null || value.isEmpty()) return "(empty)";
        String s = value.replace('\n', ' ').replace('\r', ' ').trim();
        return s.length() > max ? s.substring(0, Math.max(0, max - 3)) + "..." : s;
    }

    private boolean isTelegramPackage(String pkg) {
        return TELEGRAM_PACKAGE.equals(pkg) || TELEGRAM_BETA_PACKAGE.equals(pkg);
    }

    private void scheduleQrScreenScan() {
        if (Build.VERSION.SDK_INT < 30 || qrScanInProgress) return;

        long now = System.currentTimeMillis();
        if (now - lastQrScanAt < QR_SCAN_INTERVAL_MS) return;
        lastQrScanAt = now;
        DebugTrace.detail(this, "QR scan dijadwalkan; interval=" + QR_SCAN_INTERVAL_MS + "ms");

        handler.postDelayed(this::scanCurrentTelegramScreenForDanaQr, 250L);
    }

    private void scanCurrentTelegramScreenForDanaQr() {
        if (Build.VERSION.SDK_INT < 30 || qrScanInProgress) return;

        AccessibilityNodeInfo root = null;
        try {
            root = getRootInActiveWindow();
            if (root == null) { DebugTrace.warn(this, "QR scan: active Telegram root=null"); return; }
            CharSequence p = root.getPackageName();
            if (p == null || !isTelegramPackage(p.toString())) { DebugTrace.detail(this, "QR scan dibatalkan: active package bukan Telegram"); return; }
        } catch (Exception e) {
            return;
        } finally {
            if (root != null) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }

        qrScanInProgress = true;
        DebugTrace.detail(this, "QR scan screenshot dimulai");
        try {
            takeScreenshot(Display.DEFAULT_DISPLAY, getMainExecutor(),
                    new TakeScreenshotCallback() {
                        @Override
                        public void onSuccess(ScreenshotResult screenshot) {
                            try {
                                HardwareBuffer hb = screenshot.getHardwareBuffer();
                                if (hb == null) {
                                    qrScanInProgress = false;
                                    DebugTrace.fail(DanaAutoClickAccessibilityService.this, "QR screenshot: HardwareBuffer=null");
                                    return;
                                }

                                ColorSpace cs = screenshot.getColorSpace();
                                Bitmap hardware = Bitmap.wrapHardwareBuffer(hb, cs);

                                if (hardware == null) {
                                    hb.close();
                                    qrScanInProgress = false;
                                    return;
                                }

                                Bitmap bitmap = hardware.copy(Bitmap.Config.ARGB_8888, false);
                                hardware.recycle();
                                hb.close();
                                if (bitmap == null) {
                                    qrScanInProgress = false;
                                    DebugTrace.fail(DanaAutoClickAccessibilityService.this, "QR screenshot: bitmap conversion gagal");
                                    return;
                                }

                                qrExecutor.execute(() -> decodeDanaQr(bitmap));
                            } catch (Exception e) {
                                qrScanInProgress = false;
                                DebugTrace.fail(DanaAutoClickAccessibilityService.this, "QR screenshot setup exception=" + e.getClass().getSimpleName() + " msg=" + e.getMessage());
                                Log.w(TAG, "QR screenshot decode setup gagal: " + e.getMessage());
                            }
                        }

                        @Override
                        public void onFailure(int errorCode) {
                            qrScanInProgress = false;
                            DebugTrace.fail(DanaAutoClickAccessibilityService.this, "QR screenshot gagal code=" + errorCode);
                            Log.w(TAG, "QR screenshot gagal. code=" + errorCode);
                        }
                    });
        } catch (Exception e) {
            qrScanInProgress = false;
            DebugTrace.fail(this, "takeScreenshot exception=" + e.getClass().getSimpleName() + " msg=" + e.getMessage());
            Log.w(TAG, "takeScreenshot gagal: " + e.getMessage());
        }
    }

    private void decodeDanaQr(Bitmap bitmap) {
        try {
            InputImage image = InputImage.fromBitmap(bitmap, 0);
            qrScanner.process(image)
                    .addOnSuccessListener(qrExecutor, barcodes -> {
                        try {
                            DebugTrace.detail(this, "ML Kit QR selesai; barcodeCount=" + (barcodes == null ? 0 : barcodes.size()));
                            for (Barcode barcode : barcodes) {
                                String raw = barcode.getRawValue();
                                DebugTrace.detail(this, "QR candidate=" + DebugTrace.maskUrl(raw));
                                if (isOfficialDanaKagetUrl(raw)) {
                                    handleDanaQrUrl(raw.trim());
                                    break;
                                }
                            }
                        } finally {
                            bitmap.recycle();
                            qrScanInProgress = false;
                            DebugTrace.detail(this, "QR scan selesai");
                        }
                    })
                    .addOnFailureListener(qrExecutor, e -> {
                        try { bitmap.recycle(); } catch (Exception ignored) {}
                        qrScanInProgress = false;
                        DebugTrace.fail(this, "ML Kit QR exception=" + e.getClass().getSimpleName() + " msg=" + e.getMessage());
                        Log.w(TAG, "ML Kit gagal membaca QR: " + e.getMessage());
                    });
        } catch (Exception e) {
            try { bitmap.recycle(); } catch (Exception ignored) {}
            qrScanInProgress = false;
            DebugTrace.fail(this, "InputImage/QR decode exception=" + e.getClass().getSimpleName() + " msg=" + e.getMessage());
            Log.w(TAG, "InputImage/QR decode gagal: " + e.getMessage());
        }
    }

    private boolean isOfficialDanaKagetUrl(String raw) {
        if (raw == null) return false;
        String value = raw.trim();
        if (value.isEmpty()) return false;

        try {
            Uri u = Uri.parse(value);
            String scheme = u.getScheme();
            String host = u.getHost();
            String path = u.getPath();
            String c = u.getQueryParameter("c");

            return "https".equalsIgnoreCase(scheme)
                    && "link.dana.id".equalsIgnoreCase(host)
                    && "/danakaget".equals(path)
                    && c != null
                    && !c.trim().isEmpty();
        } catch (Exception e) {
            return false;
        }
    }

    private void handleDanaQrUrl(String rawUrl) {
        final String url = rawUrl.trim();
        if (!isOfficialDanaKagetUrl(url)) return;

        long now = System.currentTimeMillis();
        if (url.equals(lastQrUrl) && now - lastQrDetectedAt < QR_DEDUP_MS) {
            DebugTrace.warn(this, "QR duplikat diabaikan; age=" + (now - lastQrDetectedAt) + "ms");
            Log.i(TAG, "QR DANA Kaget duplikat diabaikan.");
            return;
        }
        lastQrUrl = url;
        lastQrDetectedAt = now;

        DebugTrace.start(this, "QR DANA Kaget terdeteksi");
        DebugTrace.success(this, "QR valid: " + DebugTrace.maskUrl(url));
        Log.i(TAG, "QR DANA Kaget terdeteksi");
        getSharedPreferences("dana_receiver", MODE_PRIVATE).edit()
                .putString("pending_dana_url", url)
                .apply();

        armed = true;
        armedAt = now;
        currentTapPointIndex = -1;
        currentTapNormalizedX = -1f;
        currentTapNormalizedY = -1f;
        danaUiNotified = false;
        directTapAttempts = 0;
        directTapStartedAt = 0L;
        directTapScheduled = false;
        directTapSequenceActive = false;
        danaOpenAt = 0L;
        danaTimeoutScheduled = false;
        danaLoadingWaitLogged = false;

        handler.post(() -> openDanaFromQr(url));
    }

    private void openDanaFromQr(String url) {
        Intent openDana = new Intent(Intent.ACTION_VIEW, Uri.parse(url));
        openDana.setPackage(DANA_PACKAGE);
        openDana.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_CLEAR_TOP);

        try {
            startActivity(openDana);
            DebugTrace.success(this, "Intent DANA dari QR dikirim");
            showResultNotification("📷 QR DANA Kaget terdeteksi. Membuka DANA untuk klaim...", false);
            Log.i(TAG, "QR DANA Kaget dibuka otomatis di DANA.");
            scheduleRetries();
        } catch (Exception e) {
            Log.e(TAG, "Gagal membuka DANA dari QR.", e);
            DebugTrace.fail(this, "Intent DANA dari QR gagal: " + e.getClass().getSimpleName());
            showDanaQrFallbackNotification(url);
        }
    }

    private void showDanaQrFallbackNotification(String url) {
        try {
            if (Build.VERSION.SDK_INT >= 26) {
                NotificationManager nm = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
                NotificationChannel ch = new NotificationChannel(
                        RESULT_CHANNEL, "Hasil DANA Kaget", NotificationManager.IMPORTANCE_HIGH);
                nm.createNotificationChannel(ch);
            }

            Intent openDana = new Intent(Intent.ACTION_VIEW, Uri.parse(url));
            openDana.setPackage(DANA_PACKAGE);
            openDana.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
            PendingIntent pi = PendingIntent.getActivity(
                    this, Math.abs(url.hashCode()), openDana,
                    PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);

            Notification.Builder b = Build.VERSION.SDK_INT >= 26
                    ? new Notification.Builder(this, RESULT_CHANNEL)
                    : new Notification.Builder(this);
            Notification n = b.setContentTitle("DANA Kaget QR terdeteksi")
                    .setContentText("Tekan BUKA DANA untuk melanjutkan klaim.")
                    .setSmallIcon(android.R.drawable.ic_dialog_info)
                    .setContentIntent(pi)
                    .addAction(new Notification.Action.Builder(
                            android.graphics.drawable.Icon.createWithResource(
                                    this, android.R.drawable.ic_menu_view),
                            "BUKA DANA", pi).build())
                    .setAutoCancel(true)
                    .setPriority(Notification.PRIORITY_HIGH)
                    .build();

            NotificationManager nm = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
            nm.notify(RESULT_NOTIFICATION_ID, n);
        } catch (Exception e) {
            Log.e(TAG, "Gagal membuat fallback QR notification.", e);
        }
    }

    private String eventText(AccessibilityEvent event) {
        StringBuilder sb = new StringBuilder();
        for (CharSequence t : event.getText()) if (t != null) sb.append(t).append(' ');
        if (event.getContentDescription() != null) sb.append(event.getContentDescription());
        return sb.toString();
    }

    private boolean containsIgnoreCase(String haystack, String needle) {
        return haystack != null && needle != null
                && haystack.toLowerCase().contains(needle.toLowerCase());
    }

    /**
     * Returns the package name of the currently active Accessibility window.
     *
     * V16 uses this guard before every direct gesture so a tap can only be
     * dispatched while DANA is actually the foreground/active window. Some
     * Android builds temporarily return null from getRootInActiveWindow()
     * during a transition, so we also inspect active Accessibility windows.
     */
    private String getActivePackageSafely() {
        AccessibilityNodeInfo root = null;
        try {
            root = getRootInActiveWindow();
            if (root != null) {
                CharSequence pkg = root.getPackageName();
                if (pkg != null) {
                    String value = pkg.toString().trim();
                    if (!value.isEmpty()) return value;
                }
            }
        } catch (Exception e) {
            Log.d(TAG, "getRootInActiveWindow package check gagal: " + e.getMessage());
        } finally {
            if (root != null) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }

        try {
            List<AccessibilityWindowInfo> windows = getWindows();
            if (windows != null) {
                for (AccessibilityWindowInfo window : windows) {
                    if (window == null || !window.isActive()) continue;

                    AccessibilityNodeInfo windowRoot = null;
                    try {
                        windowRoot = window.getRoot();
                        if (windowRoot != null) {
                            CharSequence pkg = windowRoot.getPackageName();
                            if (pkg != null) {
                                String value = pkg.toString().trim();
                                if (!value.isEmpty()) return value;
                            }
                        }
                    } catch (Exception ignored) {
                        // Continue checking other active windows.
                    } finally {
                        if (windowRoot != null) {
                            try { windowRoot.recycle(); } catch (Exception ignored) {}
                        }
                    }
                }
            }
        } catch (Exception e) {
            Log.d(TAG, "Accessibility active-window package check gagal: " + e.getMessage());
        }

        return "";
    }

    /**
     * V26: lightweight debug signal.
     *
     * The old implementation created a Toast and vibration for every tap/event.
     * That could wake the UI repeatedly and increase CPU/battery usage. V26 keeps
     * the log line but rate-limits it and does not create Toast/vibration.
     */
    private void debugSignal(String msg) {
        long now = System.currentTimeMillis();
        if (now - lastDebugSignalAt < 1200L) return;
        lastDebugSignalAt = now;
        Log.i(TAG, "DEBUG: " + msg);
    }

    private boolean containsRupiahAmount(String text) {
        if (text == null || text.isEmpty()) return false;
        Matcher matcher = RUPIAH_AMOUNT_PATTERN.matcher(text);
        return matcher.find();
    }

    /**
     * V26: DANA Kaget success is recognized from the result UI, e.g.
     * "Yay! Kamu dapat Rp3". A Rupiah amount is accepted only while the
     * receiver is actively processing a claim, preventing unrelated DANA
     * screens from being treated as a successful claim.
     */
    private boolean detectClaimAmountSuccess(String text) {
        if (!containsRupiahAmount(text)) return false;
        String normalized = text == null ? "" : text.toLowerCase();
        boolean contextual = normalized.contains("yay")
                || normalized.contains("kamu dapat")
                || normalized.contains("kamu mendapatkan")
                || normalized.contains("cek daftar pemenang")
                || normalized.contains("dari ");
        if (contextual) {
            DebugTrace.success(this, "V26 SUCCESS UI: Rupiah amount detected with DANA Kaget result context");
            return true;
        }
        // During the active direct-tap/claim-result window, a visible Rupiah
        // amount is itself the requested success marker.
        DebugTrace.success(this, "V26 SUCCESS UI: Rupiah amount detected during active claim");
        return true;
    }

    private void scheduleDanaTimeout() {
        if (danaTimeoutScheduled || danaOpenAt <= 0L) return;
        danaTimeoutScheduled = true;
        handler.postDelayed(() -> {
            danaTimeoutScheduled = false;
            if (danaOpenAt <= 0L) return;
            long elapsed = System.currentTimeMillis() - danaOpenAt;
            if (elapsed >= DANA_MAX_OPEN_MS && DANA_PACKAGE.equals(getActivePackageSafely())) {
                timeoutAndCloseDana();
            } else if (elapsed >= DANA_MAX_OPEN_MS) {
                timeoutAndCloseDana();
            } else {
                handler.postDelayed(this::scheduleDanaTimeout,
                        Math.max(1000L, DANA_MAX_OPEN_MS - elapsed));
            }
        }, DANA_MAX_OPEN_MS);
        DebugTrace.detail(this, "V26: DANA watchdog scheduled for " + DANA_MAX_OPEN_MS + "ms");
    }

    /**
     * Close the current DANA Kaget page using the visible top-left X when
     * possible. If the accessibility node is unavailable, use a guarded
     * top-left gesture while DANA is still foreground. BACK is only the final
     * fallback because the requested behavior is specifically to press X.
     */
    private void closeDanaPage(String reason) {
        if (!DANA_PACKAGE.equals(getActivePackageSafely())) {
            DebugTrace.detail(this, "V26 close DANA skipped: active package is not DANA; reason=" + reason);
            return;
        }

        AccessibilityNodeInfo root = null;
        try {
            root = getRootInActiveWindow();
            if (root != null && isFromDana(root)) {
                int width = getResources().getDisplayMetrics().widthPixels;
                int height = getResources().getDisplayMetrics().heightPixels;
                AccessibilityNodeInfo closeNode = findDanaCloseNode(root, width, height);
                if (closeNode != null) {
                    boolean clicked = false;
                    try {
                        clicked = closeNode.performAction(AccessibilityNodeInfo.ACTION_CLICK);
                    } catch (Exception ignored) {}
                    try { closeNode.recycle(); } catch (Exception ignored) {}
                    if (clicked) {
                        DebugTrace.success(this, "V26: DANA X ditutup via AccessibilityNode; reason=" + reason);
                        return;
                    }
                }
            }
        } catch (Exception e) {
            DebugTrace.detail(this, "V26 close X node exception=" + e.getClass().getSimpleName());
        } finally {
            if (root != null) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }

        // Screenshot/device layout in the supplied V25 test shows the X in the
        // top-left corner. Keep this fallback guarded by the DANA foreground check.
        try {
            int width = getResources().getDisplayMetrics().widthPixels;
            int height = getResources().getDisplayMetrics().heightPixels;
            float x = Math.max(24f, Math.min(width * 0.065f, width - 24f));
            float y = Math.max(24f, Math.min(height * 0.062f, height - 24f));

            Path path = new Path();
            path.moveTo(x, y);
            GestureDescription gesture = new GestureDescription.Builder()
                    .addStroke(new GestureDescription.StrokeDescription(
                            path, 0, CLOSE_GESTURE_DURATION_MS))
                    .build();

            boolean dispatched = dispatchGesture(gesture, new GestureResultCallback() {
                @Override public void onCompleted(GestureDescription g) {
                    DebugTrace.success(DanaAutoClickAccessibilityService.this,
                            "V26: DANA X fallback gesture completed; reason=" + reason);
                }

                @Override public void onCancelled(GestureDescription g) {
                    DebugTrace.warn(DanaAutoClickAccessibilityService.this,
                            "V26: DANA X fallback gesture cancelled; using BACK fallback");
                    handler.postDelayed(() -> {
                        if (DANA_PACKAGE.equals(getActivePackageSafely())) {
                            try {
                                performGlobalAction(AccessibilityService.GLOBAL_ACTION_BACK);
                            } catch (Exception ignored) {}
                        }
                    }, 120L);
                }
            }, handler);

            if (dispatched) {
                DebugTrace.detail(this, "V26: DANA X fallback gesture dispatched at (" +
                        (int) x + "," + (int) y + "); reason=" + reason);
            } else {
                try { performGlobalAction(AccessibilityService.GLOBAL_ACTION_BACK); }
                catch (Exception ignored) {}
            }
        } catch (Exception e) {
            DebugTrace.fail(this, "V26 close DANA gesture exception=" + e.getClass().getSimpleName());
            try { performGlobalAction(AccessibilityService.GLOBAL_ACTION_BACK); }
            catch (Exception ignored) {}
        }
    }

    private AccessibilityNodeInfo findDanaCloseNode(AccessibilityNodeInfo node, int width, int height) {
        if (node == null) return null;

        try {
            android.graphics.Rect r = new android.graphics.Rect();
            node.getBoundsInScreen(r);
            boolean topLeft = r.left >= 0
                    && r.top >= 0
                    && r.centerX() <= width * 0.25f
                    && r.centerY() <= height * 0.18f
                    && r.width() <= width * 0.20f
                    && r.height() <= height * 0.15f;

            String text = node.getText() == null ? "" : node.getText().toString().trim();
            String desc = node.getContentDescription() == null
                    ? "" : node.getContentDescription().toString().trim();
            String resource = node.getViewIdResourceName() == null
                    ? "" : node.getViewIdResourceName().toLowerCase();

            boolean closeLabel = text.equalsIgnoreCase("x")
                    || desc.equalsIgnoreCase("x")
                    || text.equalsIgnoreCase("close")
                    || desc.equalsIgnoreCase("close")
                    || text.equalsIgnoreCase("tutup")
                    || desc.equalsIgnoreCase("tutup")
                    || resource.contains("close")
                    || resource.contains("back");

            if (topLeft && closeLabel && (node.isClickable() || node.isFocusable())) {
                return AccessibilityNodeInfo.obtain(node);
            }

            for (int i = 0; i < node.getChildCount(); i++) {
                AccessibilityNodeInfo child = null;
                try { child = node.getChild(i); } catch (Exception ignored) {}
                if (child != null) {
                    AccessibilityNodeInfo found = findDanaCloseNode(child, width, height);
                    try { child.recycle(); } catch (Exception ignored) {}
                    if (found != null) return found;
                }
            }
        } catch (Exception ignored) {
        }
        return null;
    }

    private void timeoutAndCloseDana() {
        DebugTrace.warn(this, "V26: DANA terbuka >= 120 detik; stop semua tap dan close X");
        armed = false;
        awaitingClaimResult = false;
        clickInProgress = false;
        directTapAttempts = 0;
        directTapStartedAt = 0L;
        directTapScheduled = false;
        directTapSequenceActive = false;
        danaFallbackScheduled = false;
        danaTimeoutScheduled = false;
        danaUiNotified = false;
        shadeWaitRetries = 0;
        clickedAt = 0L;
        armedAt = 0L;

        // Clear the stale trigger so the app truly returns to standby instead
        // of reopening DANA because the old URL is still pending.
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .remove("pending_dana_url")
                .apply();

        handler.removeCallbacksAndMessages(null);
        closeDanaPage("120s timeout");
        danaOpenAt = 0L;
        showResultNotification("⏱️ DANA ditutup otomatis setelah 2 menit. Receiver kembali standby.", false);
    }

    private boolean hasPendingClaim() {
        return getSharedPreferences("dana_receiver", MODE_PRIVATE)
                .getString("pending_dana_url", "").trim().length() > 0;
    }

    private void scheduleRetries() {
        handler.removeCallbacksAndMessages(null);
        long[] delays = {0, 100, 250, 500, 900, 1500, 2500, 4000, 6000, 8000, 10000, 12000, 15000};
        for (long delay : delays) handler.postDelayed(this::tryClickDanaButton, delay);
    }

    private void tryClickDanaButton() {
        if (!armed || clickInProgress || awaitingClaimResult || directTapSequenceActive || !hasPendingClaim()) {
            DebugTrace.detail(this, "tryClick skip: armed=" + armed + " clickInProgress=" + clickInProgress
                    + " awaiting=" + awaitingClaimResult + " directActive=" + directTapSequenceActive
                    + " pending=" + hasPendingClaim());
            return;
        }

        long now = System.currentTimeMillis();
        if (armedAt == 0L) armedAt = now;
        if (now - armedAt > RETRY_WINDOW_MS) {
            armed = false;
            Log.i(TAG, "Retry window habis; tidak ada tap ke aplikasi lain.");
            return;
        }

        String activePackage = getActivePackageSafely();
        if (!DANA_PACKAGE.equals(activePackage)) {
            long danaAge = lastDanaEventAt > 0L ? now - lastDanaEventAt : Long.MAX_VALUE;
            if (danaAge <= LAST_DANA_EVENT_FALLBACK_MS) {
                DebugTrace.detail(this, "ACTIVE PACKAGE EMPTY/NON-DANA; using recent DANA event fallback: active="
                        + (activePackage.isEmpty() ? "(empty)" : activePackage)
                        + " danaAge=" + danaAge + "ms class=" + shortValue(lastDanaEventClass, 120));
                activePackage = DANA_PACKAGE;
            } else {
                DebugTrace.detail(this, "tryClick skip: activePackage="
                        + (activePackage.isEmpty() ? "(empty)" : activePackage)
                        + " lastDanaAge=" + (lastDanaEventAt > 0L ? danaAge + "ms" : "never"));
                return;
            }
        }
        DebugTrace.detail(this, "DANA foreground gate PASSED: package=" + activePackage);

        // First priority: if DANA exposes the Kaget title/instruction, start
        // the fixed-center tap immediately. The envelope animation is irrelevant
        // because the seal remains centered.
        AccessibilityNodeInfo root = null;
        String uiText = "";
        try {
            root = getRootInActiveWindow();
            if (root != null && isFromDana(root)) {
                uiText = collectNodeText(root).toLowerCase();
            }
        } catch (Exception e) {
            Log.w(TAG, "Gagal membaca root DANA: " + e.getMessage());
        } finally {
            if (root != null) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }

        DebugTrace.detail(this, "DANA UI scan: textLength=" + uiText.length() + " hasKagetHint=" + (containsIgnoreCase(uiText, ENVELOPE_HINT) || containsIgnoreCase(uiText, ENVELOPE_HINT_2)));

        boolean kagetUi = containsIgnoreCase(uiText, ENVELOPE_HINT)
                || containsIgnoreCase(uiText, ENVELOPE_HINT_2);

        if (kagetUi) {
            DebugTrace.success(this, "Hint amplop DANA terdeteksi");
            debugSignal("hint amplop terdeteksi, jadwalkan tap");
            scheduleDirectEnvelopeTap();
            return;
        }

        // Adaptive loading fallback for custom-rendered DANA screens. DANA may
        // need several seconds to finish the deep-link transition. Do NOT tap
        // immediately just because id.dana is foreground. Wait for the explicit
        // Kaget hint when available; otherwise use a conservative timeout.
        if (danaOpenAt > 0L) {
            long elapsed = now - danaOpenAt;
            if (elapsed < DIRECT_TAP_FALLBACK_AFTER_MS) {
                DebugTrace.wait(this, "DANA masih loading; elapsed=" + elapsed + "ms");
                if (!danaLoadingWaitLogged && elapsed >= 2000L) {
                    danaLoadingWaitLogged = true;
                    Log.i(TAG, "V25: DANA masih loading/merender. Menunggu halaman amplop siap (elapsed=" + elapsed + "ms).");
                }
                return;
            }

            Log.i(TAG, "V25: loading fallback tercapai. DANA foreground/event gate aktif; menjalankan fixed-center 10x tap.");
            DebugTrace.success(this, "DANA foreground confirmed by recent event; loading fallback -> DIRECT TAP");
            scheduleDirectEnvelopeTap();
            return;
        }

        // Original accessible-button flow is retained for the explicit
        // notification/button case. It never runs outside DANA.
        AccessibilityNodeInfo target = findButtonOnlyInDanaWindows();
        if (target == null) { DebugTrace.detail(this, "Accessible button BUKA DANA tidak ditemukan"); return; }

        clickInProgress = true;
        boolean clicked = clickNode(target);
        if (clicked) {
            try { target.recycle(); } catch (Exception ignored) {}
            markClickedAndWaitForClaimResult();
            return;
        }

        android.graphics.Rect bounds = new android.graphics.Rect();
        target.getBoundsInScreen(bounds);
        try { target.recycle(); } catch (Exception ignored) {}

        if (!bounds.isEmpty()) {
            tapCenter(bounds);
        } else {
            clickInProgress = false;
        }
    }

    /**
     * V15 direct-tap path. This deliberately bypasses screenshot-based envelope
     * detection. The target is a fixed point inside the center of the DANA Kaget envelope, calibrated from the provided device screen capture.
     */
    private void scheduleDirectEnvelopeTap() {
        if (!armed || awaitingClaimResult || !hasPendingClaim()) { DebugTrace.detail(this, "scheduleDirect skip: armed/awaiting/pending guard"); return; }
        String activePackage = getActivePackageSafely();
        long danaAge = lastDanaEventAt > 0L ? System.currentTimeMillis() - lastDanaEventAt : Long.MAX_VALUE;
        if (!DANA_PACKAGE.equals(activePackage) && danaAge > LAST_DANA_EVENT_FALLBACK_MS) {
            DebugTrace.detail(this, "scheduleDirect skip: activePackage="
                    + (activePackage.isEmpty() ? "(empty)" : activePackage)
                    + " lastDanaAge=" + (lastDanaEventAt > 0L ? danaAge + "ms" : "never"));
            return;
        }
        if (!DANA_PACKAGE.equals(activePackage)) {
            DebugTrace.detail(this, "scheduleDirect: recent DANA event fallback accepted; age=" + danaAge + "ms");
        }

        long now = System.currentTimeMillis();
        if (directTapStartedAt == 0L) {
            directTapStartedAt = now;
            directTapAttempts = 0;
        }

        if (directTapScheduled || directTapSequenceActive) return;

        if (now - directTapStartedAt > RETRY_WINDOW_MS) {
            Log.w(TAG, "V25: direct tap window habis.");
            DebugTrace.fail(this, "Direct tap window habis sebelum tap");
            return;
        }

        directTapScheduled = true;
        handler.postDelayed(() -> {
            directTapScheduled = false;
            startDirectTapSequence();
        }, directTapAttempts == 0 ? DIRECT_TAP_START_DELAY_MS : 0L);
    }

    /**
     * V25: ten controlled taps at the fixed center area of the DANA Kaget envelope.
     * The envelope animation moves, but its center stays fixed. We therefore
     * deliberately keep the same screen coordinate for every tap.
     *
     * We do not wait for the first gesture's completion before scheduling the
     * next attempt. This makes the final-stage interaction resilient to a
     * single dropped/cancelled gesture while keeping the tap area fixed.
     */
    private static final String PREFS_NAME = "dana_receiver";
    private static final String PREF_LEARNED_X = "learned_envelope_x";
    private static final String PREF_LEARNED_Y = "learned_envelope_y";

    private boolean hasLearnedTapPoint() {
        android.content.SharedPreferences p = getSharedPreferences(PREFS_NAME, MODE_PRIVATE);
        return p.contains(PREF_LEARNED_X) && p.contains(PREF_LEARNED_Y);
    }

    private float learnedTapX() {
        return getSharedPreferences(PREFS_NAME, MODE_PRIVATE).getFloat(PREF_LEARNED_X, -1f);
    }

    private float learnedTapY() {
        return getSharedPreferences(PREFS_NAME, MODE_PRIVATE).getFloat(PREF_LEARNED_Y, -1f);
    }

    private void saveLearnedTapPoint(float nx, float ny, int pointIndex) {
        if (nx < 0f || nx > 1f || ny < 0f || ny > 1f) return;
        getSharedPreferences(PREFS_NAME, MODE_PRIVATE).edit()
                .putFloat(PREF_LEARNED_X, nx)
                .putFloat(PREF_LEARNED_Y, ny)
                .apply();
        learnedTapPointIndex = pointIndex;
        DebugTrace.success(this, "KOORDINAT PERMANEN DISIMPAN: point=" + pointIndex
                + " normalized=(" + nx + "," + ny + ")");
        Log.i(TAG, "V25: learned envelope coordinate saved permanently: " + nx + "," + ny);
    }

    private int[] buildTapOrder() {
        int[] order = new int[DIRECT_TAP_MAX_ATTEMPTS];
        int n = 0;
        if (hasLearnedTapPoint()) {
            float lx = learnedTapX();
            float ly = learnedTapY();
            int nearest = 0;
            double best = Double.MAX_VALUE;
            for (int i = 0; i < ENVELOPE_TAP_XS.length; i++) {
                double dx = ENVELOPE_TAP_XS[i] - lx;
                double dy = ENVELOPE_TAP_YS[i] - ly;
                double d = dx * dx + dy * dy;
                if (d < best) { best = d; nearest = i; }
            }
            order[n++] = nearest;
            learnedTapPointIndex = nearest;
        }
        for (int i = 0; i < ENVELOPE_TAP_XS.length && n < order.length; i++) {
            boolean duplicate = false;
            for (int j = 0; j < n; j++) if (order[j] == i) { duplicate = true; break; }
            if (!duplicate) order[n++] = i;
        }
        return order;
    }

    private void startDirectTapSequence() {
        if (!armed || awaitingClaimResult || !hasPendingClaim()) return;
        String activePackage = getActivePackageSafely();
        long danaAge = lastDanaEventAt > 0L ? System.currentTimeMillis() - lastDanaEventAt : Long.MAX_VALUE;
        if (!DANA_PACKAGE.equals(activePackage) && danaAge > LAST_DANA_EVENT_FALLBACK_MS) {
            DebugTrace.fail(this, "Direct tap start blocked: DANA foreground not confirmed; active="
                    + (activePackage.isEmpty() ? "(empty)" : activePackage)
                    + " lastDanaAge=" + (lastDanaEventAt > 0L ? danaAge + "ms" : "never"));
            return;
        }
        if (!DANA_PACKAGE.equals(activePackage)) {
            DebugTrace.detail(this, "Direct tap start using recent DANA event fallback; age=" + danaAge + "ms");
        }
        if (directTapSequenceActive) return;

        dismissNotificationShadeSafely();
        directTapSequenceActive = true;
        directTapAttempts = 0;
        shadeWaitRetries = 0;
        directTapStartedAt = System.currentTimeMillis();
        Log.i(TAG, "V25: mulai 10-point DIRECT TAP scan; learned coordinate diprioritaskan bila tersedia.");
        DebugTrace.step(this, "Mulai direct tap sequence (maks " + DIRECT_TAP_MAX_ATTEMPTS + "x)");
        DebugTrace.detail(this, "Tap config: 10 calibrated points; learned-first=" + hasLearnedTapPoint() + " gap=" + DIRECT_TAP_ATTEMPT_GAP_MS + "ms verifyDelay=" + TAP_VERIFY_DELAY_MS + "ms");
        debugSignal("mulai tap sequence");
        dispatchNextDirectTap();
    }

    private void dispatchNextDirectTap() {
        String activePkg = getActivePackageSafely();
        long danaAge = lastDanaEventAt > 0L ? System.currentTimeMillis() - lastDanaEventAt : Long.MAX_VALUE;
        boolean danaGate = DANA_PACKAGE.equals(activePkg) || danaAge <= LAST_DANA_EVENT_FALLBACK_MS;
        if (!armed || awaitingClaimResult || !hasPendingClaim() || !danaGate) {
            DebugTrace.fail(this, "Tap dibatalkan oleh guard: armed=" + armed + " awaiting=" + awaitingClaimResult
                    + " pending=" + hasPendingClaim() + " activePkg="
                    + (activePkg.isEmpty() ? "(empty)" : activePkg)
                    + " lastDanaAge=" + (lastDanaEventAt > 0L ? danaAge + "ms" : "never"));
            debugSignal("dibatalkan: armed=" + armed + " awaiting=" + awaitingClaimResult
                    + " pending=" + hasPendingClaim() + " pkg=" + activePkg);
            finishDirectTapSequence(false);
            return;
        }

        if (directTapAttempts >= DIRECT_TAP_MAX_ATTEMPTS) {
            finishDirectTapSequence(true);
            return;
        }

        // V25 FIX ("tap buta"): danaGate di atas sengaja masih longgar (boleh lanjut
        // sampai LAST_DANA_EVENT_FALLBACK_MS=15 detik walau package aktif SAAT INI
        // bukan id.dana), supaya proses tidak berhenti gara-gara sedikit lag. Tapi itu
        // artinya sebelumnya kode bisa MENEMBAK KOORDINAT SECARA BUTA walau layar saat
        // itu sudah ketiban notification shade/app lain (mis. karena notifikasi status
        // kita sendiri memicu heads-up). Di sini kita cek ULANG package yang BENAR-BENAR
        // aktif tepat sebelum tap ditembakkan: kalau bukan id.dana, JANGAN tap buta --
        // dismiss shade dulu dan coba lagi sebentar lagi tanpa memakan jatah attempt.
        if (!DANA_PACKAGE.equals(activePkg)) {
            if (shadeWaitRetries >= MAX_SHADE_WAIT_RETRIES) {
                DebugTrace.fail(this, "Tap dibatalkan: package aktif tetap bukan DANA (" 
                        + (activePkg.isEmpty() ? "(empty)" : activePkg)
                        + ") setelah " + MAX_SHADE_WAIT_RETRIES + "x menunggu shade hilang");
                debugSignal("Dibatalkan: DANA tidak kembali ke foreground setelah menunggu shade");
                finishDirectTapSequence(false);
                return;
            }
            shadeWaitRetries++;
            DebugTrace.detail(this, "TAP " + (directTapAttempts + 1) + " ditunda ("
                    + shadeWaitRetries + "/" + MAX_SHADE_WAIT_RETRIES
                    + "): package aktif=" + (activePkg.isEmpty() ? "(empty)" : activePkg)
                    + " (bukan DANA) -> dismiss shade & coba lagi, tap TIDAK ditembakkan buta");
            debugSignal("Tap ditunda, layar bukan DANA (" + activePkg + "), dismiss shade & retry");
            dismissNotificationShadeSafely();
            handler.postDelayed(() -> {
                if (directTapSequenceActive && !awaitingClaimResult) {
                    dispatchNextDirectTap();
                }
            }, SHADE_WAIT_RETRY_DELAY_MS);
            return;
        }

        directTapAttempts++;
        final int attempt = directTapAttempts;
        clickInProgress = true;

        android.util.DisplayMetrics dm = new android.util.DisplayMetrics();
        try {
            android.view.WindowManager wm =
                    (android.view.WindowManager) getSystemService(WINDOW_SERVICE);
            if (wm != null && Build.VERSION.SDK_INT >= 17) {
                wm.getDefaultDisplay().getRealMetrics(dm);
            } else {
                dm = getResources().getDisplayMetrics();
            }
        } catch (Exception e) {
            dm = getResources().getDisplayMetrics();
        }

        // V25: try the permanently learned point first (when available),
        // then scan the remaining nine calibrated points.
        int[] tapOrder = buildTapOrder();
        int pointIndex = tapOrder[attempt - 1];
        boolean useLearned = attempt == 1 && hasLearnedTapPoint();
        currentTapPointIndex = pointIndex;
        currentTapNormalizedX = useLearned ? learnedTapX() : ENVELOPE_TAP_XS[pointIndex];
        currentTapNormalizedY = useLearned ? learnedTapY() : ENVELOPE_TAP_YS[pointIndex];
        float x = dm.widthPixels * currentTapNormalizedX;
        float y = dm.heightPixels * currentTapNormalizedY;

        Path path = new Path();
        path.moveTo(x, y);
        GestureDescription gesture = new GestureDescription.Builder()
                .addStroke(new GestureDescription.StrokeDescription(path, 0, 110))
                .build();

        DebugTrace.step(this, "TAP " + attempt + "/" + DIRECT_TAP_MAX_ATTEMPTS + " dikirim point=(" + (int)x + "," + (int)y + ") mode=" + (useLearned ? "PERMANENT_LEARNED" : "CALIBRATED_10POINT"));
        Log.i(TAG, "V25: TAP " + attempt + "/" + DIRECT_TAP_MAX_ATTEMPTS
                + " -> screen=" + dm.widthPixels + "x" + dm.heightPixels
                + ", point=(" + x + "," + y + ")");
        debugSignal("TAP " + attempt + " kirim ke (" + (int) x + "," + (int) y
                + ") layar=" + dm.widthPixels + "x" + dm.heightPixels);

        boolean dispatched;
        try {
            dispatched = dispatchGesture(gesture, new GestureResultCallback() {
                @Override public void onCompleted(GestureDescription g) {
                    clickInProgress = false;
                    Log.i(TAG, "V25: TAP " + attempt + " COMPLETED.");
                    DebugTrace.success(DanaAutoClickAccessibilityService.this, "TAP " + attempt + " COMPLETED callback");
                    DebugTrace.detail(DanaAutoClickAccessibilityService.this, "TAP " + attempt + " callback: gestureAccepted=true");
                    debugSignal("TAP " + attempt + " COMPLETED");

                    // Gesture COMPLETED only means Android accepted the gesture.
                    // Verify DANA UI before deciding whether another point is needed.
                    if (detectAndConfirmImmediateClaimResult()) {
                        directTapSequenceActive = false;
                        return;
                    }

                    handler.postDelayed(() -> {
                        if (!directTapSequenceActive || awaitingClaimResult) return;

                        boolean hintVisible = envelopeHintStillVisible();
                        DebugTrace.detail(DanaAutoClickAccessibilityService.this,
                                "TAP " + attempt + " VERIFY: envelopeHintVisible=" + hintVisible);

                        if (!hintVisible) {
                            DebugTrace.success(DanaAutoClickAccessibilityService.this,
                                    "TAP " + attempt + " VERIFY: hint hilang -> UI kemungkinan sudah berpindah; stop tap");
                            finishDirectTapSequence(true);
                            return;
                        }

                        if (attempt < DIRECT_TAP_MAX_ATTEMPTS) {
                            DebugTrace.detail(DanaAutoClickAccessibilityService.this,
                                    "TAP " + attempt + " VERIFY: hint masih ada -> lanjut titik " + (attempt + 1));
                            handler.postDelayed(() -> {
                                if (directTapSequenceActive && !awaitingClaimResult) {
                                    dispatchNextDirectTap();
                                }
                            }, DIRECT_TAP_ATTEMPT_GAP_MS);
                        } else {
                            DebugTrace.fail(DanaAutoClickAccessibilityService.this,
                                    "TAP " + attempt + " VERIFY: hint masih ada setelah 10 titik");
                            finishDirectTapSequence(true);
                        }
                    }, TAP_VERIFY_DELAY_MS);
                }

                @Override public void onCancelled(GestureDescription g) {
                    clickInProgress = false;
                    Log.w(TAG, "V25: TAP " + attempt + " CANCELLED.");
                    DebugTrace.fail(DanaAutoClickAccessibilityService.this, "TAP " + attempt + " CANCELLED callback");
                    DebugTrace.detail(DanaAutoClickAccessibilityService.this, "TAP " + attempt + " callback: gestureAccepted=false");
                    debugSignal("TAP " + attempt + " CANCELLED");

                    if (attempt < DIRECT_TAP_MAX_ATTEMPTS) {
                        handler.postDelayed(() -> {
                            if (directTapSequenceActive && !awaitingClaimResult) {
                                dispatchNextDirectTap();
                            }
                        }, 120L);
                    } else {
                        finishDirectTapSequence(false);
                    }
                }
            }, handler);
        } catch (Exception e) {
            dispatched = false;
            clickInProgress = false;
            DebugTrace.fail(this, "TAP " + attempt + " exception: " + e.getClass().getSimpleName());
            Log.w(TAG, "V25: dispatchGesture exception pada TAP " + attempt
                    + ": " + e.getMessage());
            debugSignal("TAP " + attempt + " EXCEPTION: " + e.getMessage());
        }

        if (!dispatched) {
            clickInProgress = false;
            Log.w(TAG, "V25: dispatchGesture RETURNED FALSE pada TAP " + attempt);
            DebugTrace.fail(this, "TAP " + attempt + " dispatchGesture=false (system rejected dispatch)");
            debugSignal("TAP " + attempt + " GAGAL (dispatchGesture=false)");

            if (attempt < DIRECT_TAP_MAX_ATTEMPTS) {
                handler.postDelayed(() -> {
                    if (directTapSequenceActive && !awaitingClaimResult) {
                        dispatchNextDirectTap();
                    }
                }, 120L);
            } else {
                finishDirectTapSequence(false);
            }
        }
    }

    /**
     * V25: true only while the "tap amplop buat liat DANA Kaget" hint is
     * still present in the DANA accessibility tree. Once it disappears the
     * envelope has already registered a tap and is transitioning/animating,
     * so no further tap should be sent.
     */
    private boolean envelopeHintStillVisible() {
        AccessibilityNodeInfo root = null;
        try {
            root = getRootInActiveWindow();
            if (root == null || !isFromDana(root)) return false;
            String t = collectNodeText(root).toLowerCase();
            boolean visible = containsIgnoreCase(t, ENVELOPE_HINT) || containsIgnoreCase(t, ENVELOPE_HINT_2);
            DebugTrace.detail(this, "Envelope hint visibility=" + visible + " textLength=" + t.length());
            return visible;
        } catch (Exception e) {
            return false;
        } finally {
            if (root != null) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }
    }

    private boolean detectAndConfirmImmediateClaimResult() {
        if (!hasPendingClaim()) return false;
        AccessibilityNodeInfo root = null;
        try {
            root = getRootInActiveWindow();
            if (root == null || !isFromDana(root)) return false;
            String text = collectNodeText(root).toLowerCase();
            if (detectClaimAmountSuccess(text) || containsAny(text, SUCCESS_TEXTS)) {
                awaitingClaimResult = true;
                clickedAt = System.currentTimeMillis();
                claimConfirmed(true, text);
                DebugTrace.success(this, "Hasil sukses langsung terdeteksi setelah gesture");
                Log.i(TAG, "V25: hasil sukses terdeteksi setelah gesture.");
                return true;
            }
            if (containsAny(text, FAILURE_TEXTS)) {
                awaitingClaimResult = true;
                clickedAt = System.currentTimeMillis();
                claimConfirmed(false, text);
                DebugTrace.fail(this, "Hasil gagal langsung terdeteksi setelah gesture");
                Log.i(TAG, "V25: hasil gagal terdeteksi setelah gesture.");
                return true;
            }
        } catch (Exception e) {
            Log.w(TAG, "V25: pemeriksaan hasil setelah tap gagal: " + e.getMessage());
        } finally {
            if (root != null) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }
        return false;
    }

    private void finishDirectTapSequence(boolean gesturesAccepted) {
        if (!directTapSequenceActive && !clickInProgress) return;

        directTapSequenceActive = false;
        clickInProgress = false;

        if (gesturesAccepted) {
            Log.i(TAG, "V25: 10x DIRECT TAP selesai; menunggu perubahan/hasil DANA.");
            DebugTrace.step(this, "Direct tap sequence selesai; menunggu UI hasil");
            markClickedAndWaitForClaimResult();
        } else {
            Log.w(TAG, "V25: DIRECT TAP sequence selesai tanpa semua gesture diterima.");
            DebugTrace.fail(this, "Direct tap sequence belum seluruhnya diterima");
            if (armed && hasPendingClaim() && !awaitingClaimResult) {
                scheduleDirectEnvelopeTap();
            }
        }
    }

    private AccessibilityNodeInfo findButtonOnlyInDanaWindows() {
        List<AccessibilityNodeInfo> roots = new ArrayList<>();
        try {
            AccessibilityNodeInfo active = getRootInActiveWindow();
            if (active != null) roots.add(active);
        } catch (Exception ignored) {}

        try {
            List<AccessibilityWindowInfo> windows = getWindows();
            if (windows != null) {
                for (AccessibilityWindowInfo w : windows) {
                    if (w == null) continue;
                    CharSequence title = w.getTitle();
                    // Window package is not exposed uniformly on all Android/OEM versions;
                    // node package checks below provide the actual safety gate.
                    try {
                        AccessibilityNodeInfo root = w.getRoot();
                        if (root != null) roots.add(root);
                    } catch (Exception ignored) {}
                }
            }
        } catch (Exception e) {
            Log.w(TAG, "getWindows gagal: " + e.getMessage());
        }

        AccessibilityNodeInfo found = null;
        for (AccessibilityNodeInfo root : roots) {
            if (root == null) continue;
            if (!isFromDana(root)) continue;
            found = findButton(root);
            if (found == null) found = findButtonRecursive(root);
            if (found != null) break;
        }

        for (AccessibilityNodeInfo root : roots) {
            if (root != null && root != found) {
                try { root.recycle(); } catch (Exception ignored) {}
            }
        }
        return found;
    }

    private boolean isFromDana(AccessibilityNodeInfo node) {
        CharSequence p = node.getPackageName();
        return p != null && DANA_PACKAGE.equals(p.toString());
    }

    private AccessibilityNodeInfo findButton(AccessibilityNodeInfo root) {
        try {
            List<AccessibilityNodeInfo> nodes = root.findAccessibilityNodeInfosByText(BUTTON_TEXT);
            if (nodes != null) {
                for (AccessibilityNodeInfo n : nodes) {
                    if (n != null && isFromDana(n) && isUseful(n)) return n;
                    if (n != null) try { n.recycle(); } catch (Exception ignored) {}
                }
            }
        } catch (Exception ignored) {}
        return null;
    }

    private AccessibilityNodeInfo findButtonRecursive(AccessibilityNodeInfo node) {
        if (node == null || !isFromDana(node)) return null;
        CharSequence t = node.getText();
        CharSequence d = node.getContentDescription();
        String s = t != null ? t.toString() : (d != null ? d.toString() : "");
        if (containsIgnoreCase(s, BUTTON_TEXT) && isUseful(node)) return node;

        for (int i = 0; i < node.getChildCount(); i++) {
            AccessibilityNodeInfo child = node.getChild(i);
            AccessibilityNodeInfo found = findButtonRecursive(child);
            if (found != null) return found;
            if (child != null) try { child.recycle(); } catch (Exception ignored) {}
        }
        return null;
    }

    private boolean isUseful(AccessibilityNodeInfo node) {
        if (node == null || !isFromDana(node)) return false;
        CharSequence text = node.getText();
        CharSequence desc = node.getContentDescription();
        String value = text != null ? text.toString() : (desc != null ? desc.toString() : "");
        return containsIgnoreCase(value, BUTTON_TEXT) || node.isClickable();
    }

    private boolean clickNode(AccessibilityNodeInfo node) {
        try {
            if (node.isClickable() && node.performAction(AccessibilityNodeInfo.ACTION_CLICK)) return true;
        } catch (Exception ignored) {}

        AccessibilityNodeInfo parent = null;
        try { parent = node.getParent(); } catch (Exception ignored) {}
        for (int i = 0; i < 8 && parent != null; i++) {
            try {
                if (isFromDana(parent) && parent.isClickable()
                        && parent.performAction(AccessibilityNodeInfo.ACTION_CLICK)) {
                    parent.recycle();
                    return true;
                }
                AccessibilityNodeInfo next = parent.getParent();
                parent.recycle();
                parent = next;
            } catch (Exception e) {
                try { parent.recycle(); } catch (Exception ignored) {}
                break;
            }
        }
        return false;
    }

    private void tapCenter(android.graphics.Rect bounds) {
        float x = bounds.centerX();
        float y = bounds.centerY();
        Path path = new Path();
        path.moveTo(x, y);
        GestureDescription.StrokeDescription stroke =
                new GestureDescription.StrokeDescription(path, 0, 80);
        GestureDescription gesture = new GestureDescription.Builder().addStroke(stroke).build();
        boolean dispatched = dispatchGesture(gesture, new GestureResultCallback() {
            @Override public void onCompleted(GestureDescription g) {
                Log.i(TAG, "Gesture DANA selesai. Menunggu konfirmasi hasil claim.");
                markClickedAndWaitForClaimResult();
            }
            @Override public void onCancelled(GestureDescription g) {
                clickInProgress = false;
                Log.w(TAG, "Gesture DANA dibatalkan.");
            }
        }, handler);
        if (!dispatched) clickInProgress = false;
    }

    private void markClickedAndWaitForClaimResult() {
        clickInProgress = false;
        awaitingClaimResult = true;
        clickedAt = System.currentTimeMillis();
        DebugTrace.wait(this, "Tap berhasil dikirim; menunggu konfirmasi hasil claim");
        showResultNotification("Tombol DANA tertekan. Menunggu konfirmasi claim...", false);
        Log.i(TAG, "Tombol DANA berhasil ditekan; menunggu UI konfirmasi claim.");
        pollClaimResult();
        handler.postDelayed(() -> {
            if (awaitingClaimResult && clickedAt == 0L) return;
            if (awaitingClaimResult && System.currentTimeMillis() - clickedAt >= CLAIM_CONFIRM_WINDOW_MS) {
                claimNotConfirmed();
            }
        }, CLAIM_CONFIRM_WINDOW_MS + 250L);
    }

    private void pollClaimResult() {
        if (!awaitingClaimResult) return;
        checkDanaRootForClaimResult();
        if (awaitingClaimResult && System.currentTimeMillis() - clickedAt < CLAIM_CONFIRM_WINDOW_MS) {
            handler.postDelayed(this::pollClaimResult, 1000L);
        }
    }

    private void checkDanaRootForClaimResult() {
        if (!awaitingClaimResult) return;
        try {
            AccessibilityNodeInfo root = getRootInActiveWindow();
            if (root == null || !isFromDana(root)) return;
            String allText = collectNodeText(root).toLowerCase();
            if (detectClaimAmountSuccess(allText) || containsAny(allText, SUCCESS_TEXTS)) {
                DebugTrace.success(this, "Teks hasil menunjukkan CLAIM BERHASIL");
                claimConfirmed(true, allText);
            } else if (containsAny(allText, FAILURE_TEXTS)) {
                DebugTrace.fail(this, "Teks hasil menunjukkan CLAIM GAGAL");
                claimConfirmed(false, allText);
            }
            try { root.recycle(); } catch (Exception ignored) {}
        } catch (Exception ignored) {}
    }

    private String collectNodeText(AccessibilityNodeInfo node) {
        if (node == null) return "";
        StringBuilder sb = new StringBuilder();
        CharSequence t = node.getText();
        CharSequence d = node.getContentDescription();
        if (t != null) sb.append(t).append(' ');
        if (d != null) sb.append(d).append(' ');
        for (int i = 0; i < node.getChildCount(); i++) {
            AccessibilityNodeInfo child = null;
            try { child = node.getChild(i); } catch (Exception ignored) {}
            if (child != null) {
                sb.append(collectNodeText(child)).append(' ');
                try { child.recycle(); } catch (Exception ignored) {}
            }
        }
        return sb.toString();
    }

    private void claimConfirmed(boolean success, String uiText) {
        if (success && currentTapPointIndex >= 0) {
            saveLearnedTapPoint(currentTapNormalizedX, currentTapNormalizedY, currentTapPointIndex);
        }
        String url = getSharedPreferences("dana_receiver", MODE_PRIVATE)
                .getString("pending_dana_url", "").trim();
        getSharedPreferences("dana_receiver", MODE_PRIVATE).edit()
                .remove("pending_dana_url")
                .apply();
        awaitingClaimResult = false;
        armed = false;
        clickInProgress = false;
        danaUiNotified = false;
        armedAt = 0L;
        clickedAt = 0L;
        directTapAttempts = 0;
        directTapStartedAt = 0L;
        directTapScheduled = false;
        directTapSequenceActive = false;
        danaOpenAt = 0L;
        danaTimeoutScheduled = false;
        handler.removeCallbacksAndMessages(null);

        DebugTrace.detail(this, "Claim confirmation: success=" + success + " ui=" + shortValue(uiText, 300) + " pendingUrlWas=" + DebugTrace.maskUrl(url));

        if (success) {
            DebugTrace.success(this, "CLAIM BERHASIL dikonfirmasi UI DANA");
            DebugTrace.finish(this, "Proses selesai: SUCCESS");

            // V26: success is terminal. Stop every remaining tap callback and
            // close the DANA Kaget page immediately; the service remains alive
            // and waits for the next trigger.
            handler.removeCallbacksAndMessages(null);
            closeDanaPage("claim success / Rupiah amount detected");

            showResultNotification("✅ CLAIM DANA KAGET BERHASIL dikonfirmasi oleh UI DANA.", false);
            Log.i(TAG, "CLAIM DANA BERHASIL dikonfirmasi: " + uiText);
        } else {
            DebugTrace.fail(this, "CLAIM GAGAL / tidak dapat diambil");
            DebugTrace.finish(this, "Proses selesai: FAILED");
            showResultNotification("❌ CLAIM DANA KAGET GAGAL / tidak dapat diambil.", false);
            Log.i(TAG, "CLAIM DANA gagal: " + uiText);
        }
    }

    private void claimNotConfirmed() {
        awaitingClaimResult = false;
        clickInProgress = false;
        armed = false;
        danaUiNotified = false;
        armedAt = 0L;
        clickedAt = 0L;
        directTapAttempts = 0;
        directTapStartedAt = 0L;
        directTapScheduled = false;
        directTapSequenceActive = false;
        danaOpenAt = 0L;
        handler.removeCallbacksAndMessages(null);
        DebugTrace.warn(this, "Hasil claim tidak terkonfirmasi dalam " + CLAIM_CONFIRM_WINDOW_MS + "ms");
        DebugTrace.finish(this, "Proses selesai: UNKNOWN / MANUAL CHECK");
        showResultNotification("⚠️ Tombol sudah ditekan, tetapi hasil claim belum bisa dikonfirmasi dari UI DANA.", false);
        Log.w(TAG, "Claim belum terkonfirmasi dari UI DANA; pending URL dipertahankan untuk pemeriksaan manual.");
    }

    private boolean containsAny(String text, String[] candidates) {
        if (text == null) return false;
        for (String candidate : candidates) {
            if (text.contains(candidate)) return true;
        }
        return false;
    }

    private void showResultNotification(String text, boolean keepPending) {
        try {
            // V25 FIX: kalau tap sequence SEDANG berjalan, notifikasi ini cuma status
            // sementara -- pakai channel SENYAP (importance rendah, tanpa bunyi/getar/
            // lampu/heads-up) supaya tidak ikut membuka notification shade di tengah
            // proses tap dan menyebabkan "tap buta" (lihat dispatchNextDirectTap()).
            // Setelah sequence selesai (berhasil/gagal/dikonfirmasi), notifikasi hasil
            // akhir tetap memakai channel HIGH seperti biasa supaya user tetap sadar.
            boolean quiet = directTapSequenceActive;
            String channelId = quiet ? RESULT_CHANNEL_QUIET : RESULT_CHANNEL;

            if (android.os.Build.VERSION.SDK_INT >= 26) {
                NotificationManager nm = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
                NotificationChannel ch = new NotificationChannel(
                        channelId, quiet ? "Status DANA (senyap)" : "Hasil DANA Kaget",
                        quiet ? NotificationManager.IMPORTANCE_LOW : NotificationManager.IMPORTANCE_HIGH);
                if (quiet) {
                    ch.enableVibration(false);
                    ch.setSound(null, null);
                }
                nm.createNotificationChannel(ch);
            }

            Intent open = new Intent(this, MainActivity.class);
            PendingIntent pi = PendingIntent.getActivity(this, 2002, open,
                    PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
            Notification.Builder b = android.os.Build.VERSION.SDK_INT >= 26
                    ? new Notification.Builder(this, channelId)
                    : new Notification.Builder(this);
            b.setContentTitle("DANA Native Receiver")
                    .setContentText(text)
                    .setStyle(new Notification.BigTextStyle().bigText(text))
                    .setSmallIcon(android.R.drawable.ic_dialog_info)
                    .setContentIntent(pi)
                    .setAutoCancel(true)
                    .setCategory(Notification.CATEGORY_STATUS);
            if (quiet) {
                b.setPriority(Notification.PRIORITY_LOW);
            } else {
                b.setPriority(Notification.PRIORITY_HIGH).setDefaults(Notification.DEFAULT_ALL);
            }
            Notification n = b.build();
            NotificationManager nm = (NotificationManager) getSystemService(NOTIFICATION_SERVICE);
            nm.notify(RESULT_NOTIFICATION_ID, n);
        } catch (Exception e) {
            Log.e(TAG, "Gagal membuat notifikasi hasil claim", e);
        }
    }

    @Override public void onDestroy() {
        try { qrScanner.close(); } catch (Exception ignored) {}
        qrExecutor.shutdownNow();
        handler.removeCallbacksAndMessages(null);
        super.onDestroy();
    }

    @Override public void onInterrupt() {
        armed = false;
        clickInProgress = false;
        awaitingClaimResult = false;
        clickedAt = 0L;
        directTapAttempts = 0;
        directTapStartedAt = 0L;
        directTapScheduled = false;
        directTapSequenceActive = false;
        danaOpenAt = 0L;
        danaTimeoutScheduled = false;
        Log.i(TAG, "Accessibility diinterupsi; menunggu reconnect sistem.");
    }

    public static boolean isEnabled(android.content.Context context) {
        String enabled = Settings.Secure.getString(
                context.getContentResolver(), Settings.Secure.ENABLED_ACCESSIBILITY_SERVICES);
        if (TextUtils.isEmpty(enabled)) return false;
        String target = context.getPackageName() + "/" + DanaAutoClickAccessibilityService.class.getName();
        for (String item : enabled.split(":")) if (target.equalsIgnoreCase(item)) return true;
        return false;
    }
}
