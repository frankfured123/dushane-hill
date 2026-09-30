/* ============================================================
   QLD Digital Licence — launch sequence.

   Every duration below was measured off the screen recording
   (43 fps).  The app cuts hard between screens; there are no
   cross-fades, so neither are there any here.

     0.91s  splash appears
     3.47s  → PIN                      splash held 2.56s
     5.09s  sixth digit entered
     5.47s  dots turn green, "Success" appears   (+0.38s)
     5.84s  → loading                  success held 0.35s
     7.20s  copy changes to "credentials"        (1.36s)
     8.63s  → home                                (1.43s)
     8.65s  licence card lands                    (+0.04s)
     8.86s  services land                         (+0.25s)
     8.91s  learn-more lands                      (+0.30s)

   A pressed digit is shown inside its box for ~140ms before it
   collapses to a dot (measured across all six entries).
   ============================================================ */
(function () {
  'use strict';

  var T = {
    splash:      2560,
    successWait:  380,
    successHold:  350,
    loadWallet:985,
    loadCreds:793,
    digitPeek:    140,
    reveal:      [0, 40, 250, 300]
  };
  var PIN_LENGTH = 6;

  var splash  = document.getElementById('splash');
  var pin     = document.getElementById('pin');
  var loading = document.getElementById('loading');
  var home    = document.getElementById('home');
  var wallet  = document.getElementById('wallet');
  var licence  = document.getElementById('licence');
  var showqr   = document.getElementById('showqr');
  var scanqr   = document.getElementById('scanqr');
  var messages = document.getElementById('messages');
  var settings = document.getElementById('settings');
  var addcred  = document.getElementById('addcred');
  var consent  = document.getElementById('consent');
  var byId = { home: null, wallet: null, licence: licence, showqr: showqr,
               scanqr: scanqr, messages: messages, settings: settings, addcred: addcred };

  var keypad     = document.getElementById('keypad');
  var pinDots    = document.getElementById('pinDots');
  var pinStatus  = document.getElementById('pinStatus');
  var loadText   = document.getElementById('loadingText');
  var cells      = document.querySelectorAll('.pin-cell');

  var entered = [];
  var timers  = [];

  function after(ms, fn) { timers.push(setTimeout(fn, ms)); }

  function formatStamp(d) {
    var M = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
    var h = d.getHours(), ap = h < 12 ? 'am' : 'pm';
    h = h % 12; if (h === 0) h = 12;
    var mm = String(d.getMinutes()).padStart(2, '0');
    return String(d.getDate()).padStart(2, '0') + ' ' + M[d.getMonth()] + ' ' +
           d.getFullYear() + ' ' + String(h).padStart(2, '0') + ':' + mm + ap;
  }

  /* ───────────── QR code ─────────────
     The code on Show QR is generated from whatever the licence screen says, so
     changing the details can never leave a stale code behind. Byte mode, error
     correction M and never below version 11 — the level and density read off
     the original code. The payload labels itself as sample data. */
  var QR = (function () {
    // level-M error-correction codewords per block, and block counts, v1-40
    var ECC = [-1,10,16,26,18,24,16,18,22,22,26,30,22,22,24,24,28,28,26,26,26,
               26,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28,28];
    var BLOCKS = [-1,1,1,1,2,2,4,4,4,5,5,5,8,9,9,10,10,11,13,14,16,17,17,18,
                  20,21,23,25,26,28,29,31,33,35,37,38,40,43,45,47,49];

    function rawModules(ver) {
      var r = (16 * ver + 128) * ver + 64;
      if (ver >= 2) {
        var n = Math.floor(ver / 7) + 2;
        r -= (25 * n - 10) * n - 55;
        if (ver >= 7) r -= 36;
      }
      return r;
    }

    // Reed-Solomon over GF(256), polynomial 0x11D
    function gfMul(x, y) {
      var z = 0;
      for (var i = 7; i >= 0; i--) {
        z = (z << 1) ^ ((z >>> 7) * 0x11D);
        z ^= ((y >>> i) & 1) * x;
      }
      return z;
    }
    function rsDivisor(deg) {
      var r = [], root = 1, i, j;
      for (i = 0; i < deg - 1; i++) r.push(0);
      r.push(1);
      for (i = 0; i < deg; i++) {
        for (j = 0; j < r.length; j++) {
          r[j] = gfMul(r[j], root);
          if (j + 1 < r.length) r[j] ^= r[j + 1];
        }
        root = gfMul(root, 2);
      }
      return r;
    }
    function rsRemainder(data, div) {
      var r = div.map(function () { return 0; });
      data.forEach(function (b) {
        var f = b ^ r.shift();
        r.push(0);
        div.forEach(function (c, i) { r[i] ^= gfMul(c, f); });
      });
      return r;
    }

    function maskBit(m, x, y) {
      switch (m) {
        case 0: return (x + y) % 2 === 0;
        case 1: return y % 2 === 0;
        case 2: return x % 3 === 0;
        case 3: return (x + y) % 3 === 0;
        case 4: return (Math.floor(x / 3) + Math.floor(y / 2)) % 2 === 0;
        case 5: return x * y % 2 + x * y % 3 === 0;
        case 6: return (x * y % 2 + x * y % 3) % 2 === 0;
        default: return ((x + y) % 2 + x * y % 3) % 2 === 0;
      }
    }

    function encode(text, minVer) {
      var bytes = Array.prototype.slice.call(new TextEncoder().encode(text));
      var ver, cap, i, j, k;
      for (ver = minVer || 1; ver <= 40; ver++) {
        cap = (Math.floor(rawModules(ver) / 8) - ECC[ver] * BLOCKS[ver]) * 8;
        if (4 + (ver < 10 ? 8 : 16) + bytes.length * 8 <= cap) break;
      }
      if (ver > 40) throw new Error('too long for a QR code');

      // bit stream: mode 0100, length, bytes, terminator, then pad codewords
      var bits = [];
      function put(v, n) { for (var b = n - 1; b >= 0; b--) bits.push((v >>> b) & 1); }
      put(4, 4);
      put(bytes.length, ver < 10 ? 8 : 16);
      bytes.forEach(function (b) { put(b, 8); });
      put(0, Math.min(4, cap - bits.length));
      put(0, (8 - bits.length % 8) % 8);
      for (var padByte = 0xEC; bits.length < cap; padByte ^= 0xEC ^ 0x11) put(padByte, 8);
      var data = [];
      for (i = 0; i < bits.length; i += 8) {
        for (k = 0, j = 0; j < 8; j++) k = (k << 1) | bits[i + j];
        data.push(k);
      }

      // split into blocks, add error correction, interleave
      var nb = BLOCKS[ver], ecl = ECC[ver], raw = Math.floor(rawModules(ver) / 8);
      var nShort = nb - raw % nb, shortLen = Math.floor(raw / nb);
      var div = rsDivisor(ecl), blocks = [];
      for (i = 0, k = 0; i < nb; i++) {
        var d = data.slice(k, k + shortLen - ecl + (i < nShort ? 0 : 1));
        k += d.length;
        var e = rsRemainder(d, div);
        if (i < nShort) d.push(0);
        blocks.push(d.concat(e));
      }
      var words = [];
      for (i = 0; i < blocks[0].length; i++)
        for (j = 0; j < nb; j++)
          if (i !== shortLen - ecl || j >= nShort) words.push(blocks[j][i]);

      // the matrix, with every function pattern marked so data flows around it
      var size = ver * 4 + 17, mod = [], fn = [];
      for (i = 0; i < size; i++) {
        mod.push(new Array(size).fill(false));
        fn.push(new Array(size).fill(false));
      }
      function setF(x, y, dark) { mod[y][x] = dark; fn[y][x] = true; }

      for (i = 0; i < size; i++) { setF(6, i, i % 2 === 0); setF(i, 6, i % 2 === 0); }
      [[3, 3], [size - 4, 3], [3, size - 4]].forEach(function (c) {
        for (var dy = -4; dy <= 4; dy++) for (var dx = -4; dx <= 4; dx++) {
          var x = c[0] + dx, y = c[1] + dy;
          if (x < 0 || y < 0 || x >= size || y >= size) continue;
          var dist = Math.max(Math.abs(dx), Math.abs(dy));
          setF(x, y, dist !== 2 && dist !== 4);
        }
      });
      if (ver > 1) {
        var na = Math.floor(ver / 7) + 2, al = [6];
        var step = ver === 32 ? 26 : Math.ceil((ver * 4 + 4) / (na * 2 - 2)) * 2;
        for (var p = size - 7; al.length < na; p -= step) al.splice(1, 0, p);
        for (i = 0; i < na; i++) for (j = 0; j < na; j++) {
          if ((i === 0 && j === 0) || (i === 0 && j === na - 1) || (i === na - 1 && j === 0)) continue;
          for (var ay = -2; ay <= 2; ay++) for (var ax = -2; ax <= 2; ax++)
            setF(al[i] + ax, al[j] + ay, Math.max(Math.abs(ax), Math.abs(ay)) !== 1);
        }
      }
      function drawFormat(mask) {
        var fd = mask, r = fd, fb, n;            // level M's format bits are 00
        for (n = 0; n < 10; n++) r = (r << 1) ^ ((r >>> 9) * 0x537);
        fb = ((fd << 10) | r) ^ 0x5412;
        function bit(q) { return ((fb >>> q) & 1) === 1; }
        for (n = 0; n <= 5; n++) setF(8, n, bit(n));
        setF(8, 7, bit(6)); setF(8, 8, bit(7)); setF(7, 8, bit(8));
        for (n = 9; n < 15; n++) setF(14 - n, 8, bit(n));
        for (n = 0; n < 8; n++) setF(size - 1 - n, 8, bit(n));
        for (n = 8; n < 15; n++) setF(8, size - 15 + n, bit(n));
        setF(8, size - 8, true);                 // the always-dark module
      }
      drawFormat(0);                             // reserve; redrawn per mask
      if (ver >= 7) {
        var vr = ver;
        for (i = 0; i < 12; i++) vr = (vr << 1) ^ ((vr >>> 11) * 0x1F25);
        var vb = (ver << 12) | vr;
        for (i = 0; i < 18; i++) {
          var on = ((vb >>> i) & 1) === 1, va = size - 11 + i % 3, vc = Math.floor(i / 3);
          setF(va, vc, on); setF(vc, va, on);
        }
      }

      // zig-zag the codewords in, two columns at a time, skipping the timing column
      var bi = 0, total = words.length * 8;
      for (var right = size - 1; right >= 1; right -= 2) {
        if (right === 6) right = 5;
        for (var vert = 0; vert < size; vert++) {
          for (j = 0; j < 2; j++) {
            var x = right - j, up = ((right + 1) & 2) === 0;
            var y = up ? size - 1 - vert : vert;
            if (!fn[y][x] && bi < total) {
              mod[y][x] = ((words[bi >>> 3] >>> (7 - (bi & 7))) & 1) === 1;
              bi++;
            }
          }
        }
      }

      function applyMask(m) {
        for (var yy = 0; yy < size; yy++) for (var xx = 0; xx < size; xx++)
          if (!fn[yy][xx] && maskBit(m, xx, yy)) mod[yy][xx] = !mod[yy][xx];
      }
      var FINDER_A = '10111010000', FINDER_B = '00001011101';
      function penalty() {
        var s = 0, dark = 0, yy, xx, n;
        function line(get) {
          var run = 1, str = get(0) ? '1' : '0';
          for (n = 1; n < size; n++) {
            var c = get(n);
            str += c ? '1' : '0';
            if (c === get(n - 1)) { run++; if (run === 5) s += 3; else if (run > 5) s++; }
            else run = 1;
          }
          for (n = str.indexOf(FINDER_A); n >= 0; n = str.indexOf(FINDER_A, n + 1)) s += 40;
          for (n = str.indexOf(FINDER_B); n >= 0; n = str.indexOf(FINDER_B, n + 1)) s += 40;
        }
        for (yy = 0; yy < size; yy++) line(function (q) { return mod[yy][q]; });
        for (xx = 0; xx < size; xx++) line(function (q) { return mod[q][xx]; });
        for (yy = 0; yy < size - 1; yy++) for (xx = 0; xx < size - 1; xx++) {
          var c = mod[yy][xx];
          if (c === mod[yy][xx + 1] && c === mod[yy + 1][xx] && c === mod[yy + 1][xx + 1]) s += 3;
        }
        for (yy = 0; yy < size; yy++) for (xx = 0; xx < size; xx++) if (mod[yy][xx]) dark++;
        return s + Math.floor(Math.abs(dark * 20 - size * size * 10) / (size * size)) * 10;
      }

      var best = 0, bestScore = Infinity;
      for (var m = 0; m < 8; m++) {
        applyMask(m); drawFormat(m);
        var sc = penalty();
        if (sc < bestScore) { best = m; bestScore = sc; }
        applyMask(m);                            // XOR again to undo
      }
      applyMask(best); drawFormat(best);
      return { size: size, modules: mod, version: ver, mask: best };
    }

    return { encode: encode };
  })();

  function qrSvg(q) {
    var d = '';
    for (var y = 0; y < q.size; y++) {
      for (var x = 0; x < q.size; x++) {
        if (!q.modules[y][x]) continue;
        var run = 1;
        while (x + run < q.size && q.modules[y][x + run]) run++;
        d += 'M' + x + ' ' + y + 'h' + run + 'v1h-' + run + 'z';
        x += run - 1;
      }
    }
    return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ' + q.size + ' ' + q.size +
           '" shape-rendering="crispEdges"><path fill="#000" d="' + d + '"/></svg>';
  }

  // Visible text of an element, with <br> read as a space and icons skipped.
  function txt(el) {
    if (!el) return '';
    var out = '';
    Array.prototype.forEach.call(el.childNodes, function (n) {
      if (n.nodeType === 3) out += n.nodeValue;
      else if (n.nodeName === 'BR') out += ' ';
      else if (n.nodeName !== 'svg' && n.nodeName !== 'IMG') out += txt(n);
    });
    return out.replace(/\s+/g, ' ').trim();
  }
  function rowText(label) {
    var rows = licence.querySelectorAll('.lic-row');
    for (var i = 0; i < rows.length; i++) {
      var l = rows[i].querySelector('.lic-lbl');
      if (l && txt(l).indexOf(label) === 0) return txt(rows[i].querySelector('.lic-v'));
    }
    return '';
  }
  var MON = { jan:1, feb:2, mar:3, apr:4, may:5, jun:6, jul:7, aug:8, sep:9, oct:10, nov:11, dec:12 };
  function isoDate(s) {
    var m = /^(\d{1,2})\s+([A-Za-z]{3})[A-Za-z]*\s+(\d{4})$/.exec(s);
    var mo = m && MON[m[2].toLowerCase()];
    return mo ? m[3] + '-' + pad(mo) + '-' + pad(+m[1]) : s;
  }

  function licencePayload() {
    var vals = licence.querySelectorAll('.lic-fields .lic-val');
    var cls = rowText('Class'), code = /^\(([^)]+)\)/.exec(cls);
    return [
      'QLD-DIGITAL-LICENCE',
      'SAMPLE DATA - NOT A REAL CREDENTIAL',
      'name=' + txt(licence.querySelector('.lic-name')),
      'dob=' + isoDate(txt(vals[0])),
      'licence=' + txt(vals[1]),
      'class=' + (code ? code[1] : cls),
      'type=' + rowText('Type').replace(/^\(([^)]+)\)\s*/, '$1 '),
      'expiry=' + isoDate(rowText('Expiry')),
      'card=' + rowText('Card number'),
      'address=' + rowText('Address').replace(/\s+AU$/, ''),
      'issuer=Qld TMR'
    ].join('|');
  }

  function renderQr() {
    var img = showqr.querySelector('.qr-code');
    if (!img) return;
    try {
      img.src = 'data:image/svg+xml;charset=utf-8,' +
                encodeURIComponent(qrSvg(QR.encode(licencePayload(), 11)));
    } catch (e) { /* keep whatever code is already showing */ }
  }
  // The editor's live preview calls this after rewriting the licence text.
  window.updateQr = renderQr;

  /* Show QR generates for ~1.14s, then the heading lands, then the code.
     Timings read off the recording (f1249 spinner, f1298 heading, f1307 code). */
  var qrTimers = [];
  var syncLearn = null;
  function runShowQr() {
    qrTimers.forEach(clearTimeout); qrTimers = [];
    var spin = showqr.querySelector('.qr-spin');
    var body = showqr.querySelector('.qr-content');
    var title = showqr.querySelector('.qr-title');
    var photo = showqr.querySelector('.qr-photo');
    var code  = showqr.querySelector('.qr-code');
    spin.removeAttribute('hidden'); body.hidden = true;
    photo.style.visibility = code.style.visibility = 'hidden';
    qrTimers.push(setTimeout(function () {
      spin.setAttribute('hidden', ''); body.hidden = false;
    }, 1140));
    qrTimers.push(setTimeout(function () {
      photo.style.visibility = code.style.visibility = 'visible';
    }, 1350));
  }

  /* "Information was refreshed online" reads the device clock, in the phone's
     own timezone, every time the licence is opened. */
  var MONTHS = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
  function pad(n) { return n < 10 ? '0' + n : String(n); }
  function stampNow() {
    var el = document.getElementById('refreshedAt');
    if (!el) return;
    var d = new Date();
    var h = d.getHours();
    var suffix = h < 12 ? 'am' : 'pm';
    h = h % 12; if (h === 0) h = 12;
    el.textContent = pad(d.getDate()) + ' ' + MONTHS[d.getMonth()] + ' ' + d.getFullYear() +
                     ' ' + pad(h) + ':' + pad(d.getMinutes()) + suffix;
  }
  stampNow();

  /* The sheet's rounded top corners square off against the header as soon as
     the content moves, exactly as the app does (frames 401->402 in the
     recording, and back on 434->435). */
  function watchDock(el) {
    if (!el) return;
    var sync = function () { el.classList.toggle('docked', el.scrollTop > 0); };
    el.addEventListener('scroll', sync, { passive: true });
    sync();
  }
  document.querySelectorAll('.sheet').forEach(watchDock);

  /* Pull to refresh. Measured on the wallet in the recording: the badge rides
     from under the header (centre y 360) down to y 777 while the content stays
     put; on release the sheet drops 126 and shows "Updating" for ~470 ms. */
  function pullToRefresh(screen, opts) {
    var still = opts && opts.still;
    var sheet = screen.querySelector('.sheet, .lic-scroll, .scroll-wrap');
    if (!sheet) return;
    var u = function () { return parseFloat(getComputedStyle(app).getPropertyValue('--u')) || 1; };
    var v = function () { return parseFloat(getComputedStyle(app).getPropertyValue('--v')) || 1; };

    var badge = document.createElement('div');
    badge.className = 'pull-badge';
    badge.innerHTML = '<svg viewBox="0 0 40 40" aria-hidden="true">' +
      '<path d="M31 20a11 11 0 1 1-3.6-8.1" fill="none" stroke="#620F29" stroke-width="4.4" stroke-linecap="round"/>' +
      '<path d="M9.6 25.6 8 16.4l9.2 1.6z" fill="#620F29"/></svg>';
    var label = document.createElement('div');
    label.className = 'pull-label';
    label.innerHTML = '<svg class="pull-spin" viewBox="0 0 54 54" aria-hidden="true">' +
      '<circle cx="27" cy="27" r="23"/></svg><span>Updating</span>';
    screen.appendChild(badge); screen.appendChild(label);

    var TRAVEL = 417, TRIGGER = 300;      /* reference units */
    var y0 = null, pull = 0, busy = false;

    function move(px) {
      badge.style.transform = 'translateY(' + (px * v()) + 'px)';
      badge.classList.toggle('on', px > 8);
    }
    function reset(animate) {
      badge.classList.toggle('snap', !!animate);
      pull = 0; move(0); badge.classList.remove('on', 'spin');
      setTimeout(function () { badge.classList.remove('snap'); }, 260);
    }
    function refresh() {
      busy = true;
      badge.classList.add('snap'); badge.classList.remove('on', 'spin');
      badge.style.transform = 'translateY(0)';
      if (!still) sheet.classList.add('settle', 'refreshing');
      if (!still) label.classList.add('on');
      after(470, function () {
        sheet.classList.remove('refreshing');
        label.classList.remove('on');
        after(260, function () { sheet.classList.remove('settle'); busy = false; });
        var stamp = document.getElementById('refreshStamp');
        if (stamp) stamp.textContent = formatStamp(new Date());
      });
    }
    function start(cy) { if (sheet.scrollTop <= 0 && !busy) { y0 = cy; badge.classList.remove('snap'); } }
    function drag(cy, e) {
      if (y0 === null) return;
      var d = (cy - y0) / v();
      if (d <= 0) { pull = 0; move(0); return; }
      if (e && e.cancelable) e.preventDefault();
      pull = Math.min(d * 0.62, TRAVEL);
      move(pull);
    }
    function end() {
      if (y0 === null) return;
      y0 = null;
      if (pull >= TRIGGER) refresh(); else reset(true);
    }
    sheet.addEventListener('touchstart', function (e) { start(e.touches[0].clientY); }, { passive: true });
    sheet.addEventListener('touchmove',  function (e) { drag(e.touches[0].clientY, e); }, { passive: false });
    sheet.addEventListener('touchend', end);
    sheet.addEventListener('touchcancel', end);
    sheet.addEventListener('mousedown', function (e) { start(e.clientY); });
    window.addEventListener('mousemove', function (e) { if (y0 !== null) drag(e.clientY, e); });
    window.addEventListener('mouseup', end);
    screen.__pull = { refresh: refresh, reset: reset };
  }
  [home, wallet].forEach(pullToRefresh);
  pullToRefresh(licence, { still: true });

  /* The Learn more row shows a left chevron once it has been swiped, and drops
     the right one at the end — same as the app. */
  (function () {
    var strip = document.querySelector('.learn');
    var row   = document.querySelector('.view-all');
    if (!strip || !row) return;
    var sync = function () {
      var max = strip.scrollWidth - strip.clientWidth;
      row.classList.toggle('has-prev', strip.scrollLeft > 4);
      row.classList.toggle('at-end',   strip.scrollLeft >= max - 4);
    };
    strip.addEventListener('scroll', sync, { passive: true });
    window.addEventListener('load', sync);
    syncLearn = sync;                 /* re-run once #home is actually laid out */
    sync();
  })();

  /* Every screen goes back to the top when you open it */
  function resetScroll(target) {
    if (!target) return;
    target.scrollTop = 0;
    var w = target.querySelector('.scroll-wrap'); if (w) w.scrollTop = 0;
    var s = target.querySelector('.sheet');
    if (s) { s.scrollTop = 0; s.classList.remove('docked'); }
    var l = target.querySelector('.lic-scroll'); if (l) l.scrollTop = 0;
  }

  /* Hard cut, the way the app switches screens */
  function show(screen) {
    [splash, pin, loading, home, wallet, licence, showqr, scanqr, messages, settings, addcred]
      .forEach(function (s) { s.hidden = (s !== screen); });
    consent.hidden = true;
    if (screen === licence) stampNow();
    if (screen === home && syncLearn) syncLearn();
    if (screen === showqr) runShowQr();
    else { qrTimers.forEach(clearTimeout); qrTimers = []; }
  }

  (function greet() {
    var h = new Date().getHours();
    document.getElementById('greeting').textContent =
      h >= 5  && h < 12 ? 'Good morning'   :
      h >= 12 && h < 18 ? 'Good afternoon' :
      h >= 18 && h < 22 ? 'Good evening'   : 'Good night';
  })();

  /* Haptics. navigator.vibrate is supported by Chrome on Android and needs a
     real user gesture, so it is fired from pointerdown rather than click.
     iOS Safari does not implement the Vibration API at all — nothing to do there. */
  function buzz() {
    try { if (navigator.vibrate) navigator.vibrate(35); } catch (e) { /* unsupported */ }
  }

  /* Press feedback: instant tint plus a ripple from the touch point */
  function ripple(key, clientX, clientY) {
    var r = key.getBoundingClientRect();
    var size = Math.max(r.width, r.height) * 1.15;
    var el = document.createElement('span');
    el.className = 'ripple';
    el.style.width = el.style.height = size + 'px';
    el.style.left = (clientX - r.left) + 'px';
    el.style.top  = (clientY - r.top) + 'px';
    key.appendChild(el);
    setTimeout(function () { el.remove(); }, 460);
  }

  keypad.addEventListener('pointerdown', function (e) {
    var key = e.target.closest('.key');
    if (!key || !key.dataset.key || keypad.classList.contains('locked')) return;
    buzz();
    key.classList.add('pressed');
    ripple(key, e.clientX, e.clientY);
  });
  ['pointerup', 'pointercancel', 'pointerleave'].forEach(function (evt) {
    keypad.addEventListener(evt, function (e) {
      var key = e.target.closest('.key');
      if (key) key.classList.remove('pressed');
    });
  });

  function paintDots() {
    for (var i = 0; i < cells.length; i++) {
      var on = i < entered.length;
      cells[i].classList.toggle('filled', on && !cells[i].classList.contains('revealed'));
      if (!on) {
        cells[i].classList.remove('revealed');
        cells[i].textContent = '';
      }
    }
  }

  /* The app prints the digit in its box, then collapses it to a dot */
  function revealThenMask(cell, digit) {
    cell.textContent = digit;
    cell.classList.add('revealed');
    cell.classList.remove('filled');
    after(T.digitPeek, function () {
      cell.textContent = '';
      cell.classList.remove('revealed');
      cell.classList.add('filled');
    });
  }

  function press(value) {
    if (value === 'del') { entered.pop(); paintDots(); return; }
    if (entered.length >= PIN_LENGTH) return;
    entered.push(value);
    revealThenMask(cells[entered.length - 1], value);
    paintDots();
    if (entered.length === PIN_LENGTH) verify();
  }

  function verify() {
    keypad.classList.add('locked');
    after(T.successWait + T.digitPeek, function () {
      for (var i = 0; i < cells.length; i++) {
        cells[i].textContent = '';
        cells[i].classList.remove('revealed');
        cells[i].classList.add('filled');
      }
      pinDots.classList.add('verified');
      pinStatus.classList.add('show');
      after(T.successHold, runLoading);
    });
  }

  function runLoading() {
    loadText.textContent = 'Fetching your digital wallet';
    show(loading);
    after(T.loadWallet, function () {
      loadText.textContent = 'Fetching your credentials';
      after(T.loadCreds, enterHome);
    });
  }

  function enterHome() {
    show(home);
    document.querySelectorAll('#home .reveal').forEach(function (el) {
      after(T.reveal[+el.dataset.step] || 0, function () { el.classList.add('in'); });
    });
  }

  keypad.addEventListener('click', function (e) {
    var key = e.target.closest('.key');
    if (key && key.dataset.key) press(key.dataset.key);
  });

  /* Hardware keyboard, useful when testing on a desktop */
  document.addEventListener('keydown', function (e) {
    if (pin.hidden) return;
    if (e.key >= '0' && e.key <= '9') { buzz(); press(e.key); }
    else if (e.key === 'Backspace') { e.preventDefault(); buzz(); press('del'); }
  });

  /* Tab bar: Home and Wallet are wired up, the rest are inert as in the app */
  var cameFrom = home;

  byId.home = home; byId.wallet = wallet;

  function inApp() {
    return !(splash.hidden && pin.hidden && loading.hidden) === false;
  }

  document.addEventListener('click', function (e) {
    if (!splash.hidden || !pin.hidden || !loading.hidden) return;

    /* Consent dialog owns the click while it is up */
    if (!consent.hidden) {
      var choice = e.target.closest('[data-consent]');
      if (choice) consent.hidden = true;
      return;
    }

    var tab = e.target.closest('.tab[data-go]');
    if (tab) {
      var target = byId[tab.dataset.go];
      if (target) {
        resetScroll(target);
        show(target);
      }
      return;
    }

    /* Opening a licence remembers where it was opened from */
    var card = e.target.closest('.licence');
    if (card && (!home.hidden || !wallet.hidden)) {
      cameFrom = home.hidden ? wallet : home;
      resetScroll(licence);
      show(licence);
      return;
    }

    if (e.target.closest('.add-btn')) { cameFrom = wallet; show(addcred); return; }
    if (e.target.closest('.share-pdf')) { consent.hidden = false; return; }
    if (e.target.closest('.topbar .cog')) { resetScroll(settings); show(settings); return; }
    if (e.target.closest('[data-back]')) show(settings.hidden ? cameFrom : home);
  });

  renderQr();
  after(T.splash, function () { show(pin); });
})();
