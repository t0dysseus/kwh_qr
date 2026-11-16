/*
 * Eigener QR-Code-Encoder, ohne fremde Bibliothek.
 * - Datenmodus: Byte (UTF-8)
 * - Fehlerkorrektur: H (höchste Stufe, nötig für das Logo in der Mitte)
 * - Versionen 1 bis 40, die kleinste passende wird automatisch gewählt
 * Der QR-Standard (ISO/IEC 18004) ist frei nutzbar.
 */
(function (global) {
  "use strict";

  // Fehlerkorrektur-Codewörter pro Block und Anzahl Blöcke, Stufe H, Index = Version
  var ECC_PER_BLOCK = [0, 17, 28, 22, 16, 22, 28, 26, 26, 24, 28, 24, 28, 22, 24, 24, 30, 28, 28, 26, 28, 30, 24, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30];
  var NUM_BLOCKS = [0, 1, 1, 2, 4, 4, 4, 5, 6, 8, 8, 11, 11, 16, 16, 18, 16, 19, 21, 25, 25, 25, 34, 30, 32, 35, 37, 40, 42, 45, 48, 51, 54, 57, 60, 63, 66, 70, 74, 77, 81];

  var MIN_VERSION = 5; // genug Platz um das Logo, ohne Eckmuster zu berühren
  var LOGO_MAX_SHARE = 0.28; // Logo-Fläche: höchstens 28 % der Breite

  // ---------- Hilfsfunktionen ----------

  function bit(value, i) {
    return ((value >>> i) & 1) !== 0;
  }

  function rawModules(ver) {
    var result = (16 * ver + 128) * ver + 64;
    if (ver >= 2) {
      var n = Math.floor(ver / 7) + 2;
      result -= (25 * n - 10) * n - 55;
      if (ver >= 7) result -= 36;
    }
    return result;
  }

  function dataCodewords(ver) {
    return Math.floor(rawModules(ver) / 8) - ECC_PER_BLOCK[ver] * NUM_BLOCKS[ver];
  }

  function alignmentPositions(ver) {
    if (ver === 1) return [];
    var n = Math.floor(ver / 7) + 2;
    var size = ver * 4 + 17;
    var step = ver === 32 ? 26 : Math.ceil((ver * 4 + 4) / (n * 2 - 2)) * 2;
    var result = [6];
    for (var pos = size - 7; result.length < n; pos -= step) result.splice(1, 0, pos);
    return result;
  }

  // ---------- Reed-Solomon über GF(256), Polynom 0x11D ----------

  function gfMultiply(x, y) {
    var z = 0;
    for (var i = 7; i >= 0; i--) {
      z = (z << 1) ^ ((z >>> 7) * 0x11d);
      z ^= ((y >>> i) & 1) * x;
    }
    return z;
  }

  function rsDivisor(degree) {
    var r = [];
    for (var i = 0; i < degree; i++) r.push(0);
    r[degree - 1] = 1;
    var root = 1;
    for (var k = 0; k < degree; k++) {
      for (var j = 0; j < r.length; j++) {
        r[j] = gfMultiply(r[j], root);
        if (j + 1 < r.length) r[j] ^= r[j + 1];
      }
      root = gfMultiply(root, 0x02);
    }
    return r;
  }

  function rsRemainder(data, divisor) {
    var r = divisor.map(function () { return 0; });
    data.forEach(function (b) {
      var factor = b ^ r.shift();
      r.push(0);
      divisor.forEach(function (c, i) { r[i] ^= gfMultiply(c, factor); });
    });
    return r;
  }

  // ---------- Daten kodieren ----------

  function utf8Bytes(text) {
    if (typeof TextEncoder !== "undefined") return Array.from(new TextEncoder().encode(text));
    var s = unescape(encodeURIComponent(text));
    var out = [];
    for (var i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
    return out;
  }

  function buildDataCodewords(bytes, ver) {
    var bits = [];
    function push(value, len) {
      for (var i = len - 1; i >= 0; i--) bits.push((value >>> i) & 1);
    }
    push(0x4, 4); // Byte-Modus
    push(bytes.length, ver <= 9 ? 8 : 16);
    bytes.forEach(function (b) { push(b, 8); });

    var capacityBits = dataCodewords(ver) * 8;
    push(0, Math.min(4, capacityBits - bits.length)); // Abschluss
    while (bits.length % 8 !== 0) bits.push(0);
    var codewords = [];
    for (var i = 0; i < bits.length; i += 8) {
      var v = 0;
      for (var j = 0; j < 8; j++) v = (v << 1) | bits[i + j];
      codewords.push(v);
    }
    for (var pad = 0xec; codewords.length < dataCodewords(ver); pad ^= 0xec ^ 0x11) codewords.push(pad);
    return codewords;
  }

  function addEccAndInterleave(data, ver) {
    var numBlocks = NUM_BLOCKS[ver];
    var eccLen = ECC_PER_BLOCK[ver];
    var raw = Math.floor(rawModules(ver) / 8);
    var numShort = numBlocks - (raw % numBlocks);
    var shortLen = Math.floor(raw / numBlocks);
    var divisor = rsDivisor(eccLen);
    var blocks = [];
    for (var i = 0, k = 0; i < numBlocks; i++) {
      var datLen = shortLen - eccLen + (i < numShort ? 0 : 1);
      var dat = data.slice(k, k + datLen);
      k += datLen;
      var ecc = rsRemainder(dat, divisor);
      if (i < numShort) dat.push(0); // Platzhalter, wird beim Mischen übersprungen
      blocks.push(dat.concat(ecc));
    }
    var result = [];
    for (var col = 0; col < blocks[0].length; col++) {
      for (var b = 0; b < blocks.length; b++) {
        if (col !== shortLen - eccLen || b >= numShort) result.push(blocks[b][col]);
      }
    }
    return result;
  }

  // ---------- Matrix aufbauen ----------

  function Matrix(ver) {
    this.version = ver;
    this.size = ver * 4 + 17;
    this.modules = [];
    this.isFunction = [];
    for (var y = 0; y < this.size; y++) {
      var row = [], fn = [];
      for (var x = 0; x < this.size; x++) { row.push(false); fn.push(false); }
      this.modules.push(row);
      this.isFunction.push(fn);
    }
  }

  Matrix.prototype.setFunction = function (x, y, dark) {
    this.modules[y][x] = dark;
    this.isFunction[y][x] = true;
  };

  Matrix.prototype.drawFinder = function (cx, cy) {
    for (var dy = -4; dy <= 4; dy++) {
      for (var dx = -4; dx <= 4; dx++) {
        var dist = Math.max(Math.abs(dx), Math.abs(dy));
        var x = cx + dx, y = cy + dy;
        if (x >= 0 && x < this.size && y >= 0 && y < this.size) {
          this.setFunction(x, y, dist !== 2 && dist !== 4);
        }
      }
    }
  };

  Matrix.prototype.drawAlignment = function (cx, cy) {
    for (var dy = -2; dy <= 2; dy++) {
      for (var dx = -2; dx <= 2; dx++) {
        this.setFunction(cx + dx, cy + dy, Math.max(Math.abs(dx), Math.abs(dy)) !== 1);
      }
    }
  };

  Matrix.prototype.drawFormat = function (mask) {
    var data = (2 << 3) | mask; // Stufe H = 2
    var rem = data;
    for (var i = 0; i < 10; i++) rem = (rem << 1) ^ ((rem >>> 9) * 0x537);
    var bits = ((data << 10) | rem) ^ 0x5412;
    var s = this.size;
    for (i = 0; i <= 5; i++) this.setFunction(8, i, bit(bits, i));
    this.setFunction(8, 7, bit(bits, 6));
    this.setFunction(8, 8, bit(bits, 7));
    this.setFunction(7, 8, bit(bits, 8));
    for (i = 9; i < 15; i++) this.setFunction(14 - i, 8, bit(bits, i));
    for (i = 0; i < 8; i++) this.setFunction(s - 1 - i, 8, bit(bits, i));
    for (i = 8; i < 15; i++) this.setFunction(8, s - 15 + i, bit(bits, i));
    this.setFunction(8, s - 8, true); // festes dunkles Modul
  };

  Matrix.prototype.drawVersion = function () {
    if (this.version < 7) return;
    var rem = this.version;
    for (var i = 0; i < 12; i++) rem = (rem << 1) ^ ((rem >>> 11) * 0x1f25);
    var bits = (this.version << 12) | rem;
    for (i = 0; i < 18; i++) {
      var dark = bit(bits, i);
      var a = this.size - 11 + (i % 3);
      var b = Math.floor(i / 3);
      this.setFunction(a, b, dark);
      this.setFunction(b, a, dark);
    }
  };

  Matrix.prototype.drawFunctionPatterns = function () {
    var s = this.size, i;
    for (i = 0; i < s; i++) {
      this.setFunction(6, i, i % 2 === 0);
      this.setFunction(i, 6, i % 2 === 0);
    }
    this.drawFinder(3, 3);
    this.drawFinder(s - 4, 3);
    this.drawFinder(3, s - 4);
    var pos = alignmentPositions(this.version);
    var n = pos.length;
    for (i = 0; i < n; i++) {
      for (var j = 0; j < n; j++) {
        if ((i === 0 && j === 0) || (i === 0 && j === n - 1) || (i === n - 1 && j === 0)) continue;
        this.drawAlignment(pos[i], pos[j]);
      }
    }
    this.drawFormat(0); // Platz reservieren, wird später überschrieben
    this.drawVersion();
  };

  Matrix.prototype.drawCodewords = function (data) {
    var s = this.size, i = 0;
    for (var right = s - 1; right >= 1; right -= 2) {
      if (right === 6) right = 5;
      for (var vert = 0; vert < s; vert++) {
        for (var j = 0; j < 2; j++) {
          var x = right - j;
          var upward = ((right + 1) & 2) === 0;
          var y = upward ? s - 1 - vert : vert;
          if (!this.isFunction[y][x] && i < data.length * 8) {
            this.modules[y][x] = bit(data[i >>> 3], 7 - (i & 7));
            i++;
          }
        }
      }
    }
  };

  Matrix.prototype.applyMask = function (mask) {
    for (var y = 0; y < this.size; y++) {
      for (var x = 0; x < this.size; x++) {
        var invert;
        switch (mask) {
          case 0: invert = (x + y) % 2 === 0; break;
          case 1: invert = y % 2 === 0; break;
          case 2: invert = x % 3 === 0; break;
          case 3: invert = (x + y) % 3 === 0; break;
          case 4: invert = (Math.floor(x / 3) + Math.floor(y / 2)) % 2 === 0; break;
          case 5: invert = ((x * y) % 2) + ((x * y) % 3) === 0; break;
          case 6: invert = (((x * y) % 2) + ((x * y) % 3)) % 2 === 0; break;
          default: invert = (((x + y) % 2) + ((x * y) % 3)) % 2 === 0; break;
        }
        if (!this.isFunction[y][x] && invert) this.modules[y][x] = !this.modules[y][x];
      }
    }
  };

  Matrix.prototype.penalty = function () {
    var s = this.size, m = this.modules, score = 0, x, y, run, i;

    // Regel 1: Reihen und Spalten mit 5 oder mehr gleichen Modulen
    for (var dir = 0; dir < 2; dir++) {
      for (var a = 0; a < s; a++) {
        run = 1;
        for (var b = 1; b < s; b++) {
          var cur = dir === 0 ? m[a][b] : m[b][a];
          var prev = dir === 0 ? m[a][b - 1] : m[b - 1][a];
          if (cur === prev) {
            run++;
            if (run === 5) score += 3;
            else if (run > 5) score += 1;
          } else {
            run = 1;
          }
        }
      }
    }

    // Regel 2: 2x2-Blöcke gleicher Farbe
    for (y = 0; y < s - 1; y++) {
      for (x = 0; x < s - 1; x++) {
        var c = m[y][x];
        if (c === m[y][x + 1] && c === m[y + 1][x] && c === m[y + 1][x + 1]) score += 3;
      }
    }

    // Regel 3: Muster, die einem Eckmuster ähneln (1:1:3:1:1 mit 4 hellen Modulen daneben)
    var pat1 = "10111010000", pat2 = "00001011101";
    for (dir = 0; dir < 2; dir++) {
      for (a = 0; a < s; a++) {
        var str = "";
        for (b = 0; b < s; b++) str += (dir === 0 ? m[a][b] : m[b][a]) ? "1" : "0";
        for (i = 0; i + 11 <= s; i++) {
          var part = str.substr(i, 11);
          if (part === pat1 || part === pat2) score += 40;
        }
      }
    }

    // Regel 4: Anteil dunkler Module
    var dark = 0;
    for (y = 0; y < s; y++) for (x = 0; x < s; x++) if (m[y][x]) dark++;
    var total = s * s;
    var k = Math.ceil(Math.abs(dark * 20 - total * 10) / total) - 1;
    score += k * 10;
    return score;
  };

  // ---------- Öffentliche Funktionen ----------

  /**
   * Erzeugt den QR-Code für einen Text.
   * Rückgabe: { size, version, mask, modules } mit modules[y][x] === true für dunkel.
   * Wirft einen Error, wenn der Text zu lang ist.
   */
  function encode(text, options) {
    options = options || {};
    var minVersion = options.minVersion || MIN_VERSION;
    var bytes = utf8Bytes(text);
    var ver = minVersion;
    for (; ver <= 40; ver++) {
      var needed = 4 + (ver <= 9 ? 8 : 16) + bytes.length * 8;
      if (needed <= dataCodewords(ver) * 8) break;
    }
    if (ver > 40) throw new Error("TOO_LONG");

    var data = addEccAndInterleave(buildDataCodewords(bytes, ver), ver);
    var matrix = new Matrix(ver);
    matrix.drawFunctionPatterns();
    matrix.drawCodewords(data);

    var forced = options.mask;
    var best = -1, bestScore = Infinity;
    for (var mask = 0; mask < 8; mask++) {
      if (typeof forced === "number" && mask !== forced) continue;
      matrix.applyMask(mask);
      matrix.drawFormat(mask);
      var p = matrix.penalty();
      if (p < bestScore) { bestScore = p; best = mask; }
      matrix.applyMask(mask); // Maske wieder entfernen
    }
    matrix.applyMask(best);
    matrix.drawFormat(best);
    return { size: matrix.size, version: ver, mask: best, modules: matrix.modules };
  }

  /**
   * Zeichnet den QR-Code auf ein Canvas, mit freigestellter Fläche und Logo in der Mitte.
   * options: dark, light (Farben), logo (Bildobjekt oder null), targetPx (ca. Zielbreite)
   */
  function draw(canvas, qr, options) {
    options = options || {};
    var dark = options.dark || "#000000";
    var light = options.light || "#ffffff";
    var logo = options.logo || null;
    var quiet = 4; // Ruhezone in Modulen
    var total = qr.size + quiet * 2;
    var scale = Math.max(6, Math.floor((options.targetPx || 1080) / total));
    var px = total * scale;
    canvas.width = px;
    canvas.height = px;
    var ctx = canvas.getContext("2d");
    ctx.fillStyle = light;
    ctx.fillRect(0, 0, px, px);
    ctx.fillStyle = dark;
    for (var y = 0; y < qr.size; y++) {
      var x = 0;
      while (x < qr.size) {
        if (!qr.modules[y][x]) { x++; continue; }
        var start = x;
        while (x < qr.size && qr.modules[y][x]) x++;
        ctx.fillRect((quiet + start) * scale, (quiet + y) * scale, (x - start) * scale, scale);
      }
    }
    if (logo) {
      // Quadrat aus ungerader Modulzahl, exakt zentriert und an das Raster angelehnt
      var box = Math.floor(qr.size * LOGO_MAX_SHARE);
      if (box % 2 === 0) box -= 1;
      var offset = (qr.size - box) / 2;
      ctx.fillStyle = light;
      ctx.fillRect((quiet + offset) * scale, (quiet + offset) * scale, box * scale, box * scale);
      var side = (box - 1) * scale; // halbes Modul Luft an jeder Seite
      var lw = logo.naturalWidth || logo.width;
      var lh = logo.naturalHeight || logo.height;
      var ratio = Math.min(side / lw, side / lh);
      var w = lw * ratio, h = lh * ratio;
      var cx = px / 2, cy = px / 2;
      ctx.drawImage(logo, cx - w / 2, cy - h / 2, w, h);
    }
    return px;
  }

  var api = { encode: encode, draw: draw };
  if (typeof module !== "undefined" && module.exports) module.exports = api;
  else global.QR = api;
})(typeof window !== "undefined" ? window : this);
