"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4){var _5=E(_3);return (_5._==0)?E(_4):new T2(1,_5.a,new T(function(){return B(_2(_5.b,_4));}));},_6=__Z,_7=0,_8=function(_9,_){while(1){var _a=E(_9);if(!_a._){return _7;}else{var _b=_a.b,_c=E(_a.a);switch(_c._){case 0:var _d=B(A1(_c.a,_));_9=B(_2(_b,new T2(1,_d,_6)));continue;case 1:_9=B(_2(_b,_c.a));continue;default:_9=_b;continue;}}}},_e=function(_f,_g,_){var _h=E(_f);switch(_h._){case 0:var _i=B(A1(_h.a,_));return new F(function(){return _8(B(_2(_g,new T2(1,_i,_6))),_);});break;case 1:return new F(function(){return _8(B(_2(_g,_h.a)),_);});break;default:return new F(function(){return _8(_g,_);});}},_j=function(_k,_l,_){var _m=B(A1(_k,_)),_n=B(A1(_l,_));return _m;},_o=function(_p,_q,_){var _r=B(A1(_p,_)),_s=B(A1(_q,_));return new T(function(){return B(A1(_r,_s));});},_t=function(_u,_v,_){var _w=B(A1(_v,_));return _u;},_x=function(_y,_z,_){var _A=B(A1(_z,_));return new T(function(){return B(A1(_y,_A));});},_B=new T2(0,_x,_t),_C=function(_D,_){return _D;},_E=function(_F,_G,_){var _H=B(A1(_F,_));return new F(function(){return A1(_G,_);});},_I=new T5(0,_B,_C,_o,_E,_j),_J=new T(function(){return B(unCStr("base"));}),_K=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_L=new T(function(){return B(unCStr("IOException"));}),_M=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_J,_K,_L),_N=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_M,_6,_6),_O=function(_P){return E(_N);},_Q=function(_R){return E(E(_R).a);},_S=function(_T,_U,_V){var _W=B(A1(_T,_)),_X=B(A1(_U,_)),_Y=hs_eqWord64(_W.a,_X.a);if(!_Y){return __Z;}else{var _Z=hs_eqWord64(_W.b,_X.b);return (!_Z)?__Z:new T1(1,_V);}},_10=function(_11){var _12=E(_11);return new F(function(){return _S(B(_Q(_12.a)),_O,_12.b);});},_13=new T(function(){return B(unCStr(": "));}),_14=new T(function(){return B(unCStr(")"));}),_15=new T(function(){return B(unCStr(" ("));}),_16=new T(function(){return B(unCStr("interrupted"));}),_17=new T(function(){return B(unCStr("system error"));}),_18=new T(function(){return B(unCStr("unsatisified constraints"));}),_19=new T(function(){return B(unCStr("user error"));}),_1a=new T(function(){return B(unCStr("permission denied"));}),_1b=new T(function(){return B(unCStr("illegal operation"));}),_1c=new T(function(){return B(unCStr("end of file"));}),_1d=new T(function(){return B(unCStr("resource exhausted"));}),_1e=new T(function(){return B(unCStr("resource busy"));}),_1f=new T(function(){return B(unCStr("does not exist"));}),_1g=new T(function(){return B(unCStr("already exists"));}),_1h=new T(function(){return B(unCStr("resource vanished"));}),_1i=new T(function(){return B(unCStr("timeout"));}),_1j=new T(function(){return B(unCStr("unsupported operation"));}),_1k=new T(function(){return B(unCStr("hardware fault"));}),_1l=new T(function(){return B(unCStr("inappropriate type"));}),_1m=new T(function(){return B(unCStr("invalid argument"));}),_1n=new T(function(){return B(unCStr("failed"));}),_1o=new T(function(){return B(unCStr("protocol error"));}),_1p=function(_1q,_1r){switch(E(_1q)){case 0:return new F(function(){return _2(_1g,_1r);});break;case 1:return new F(function(){return _2(_1f,_1r);});break;case 2:return new F(function(){return _2(_1e,_1r);});break;case 3:return new F(function(){return _2(_1d,_1r);});break;case 4:return new F(function(){return _2(_1c,_1r);});break;case 5:return new F(function(){return _2(_1b,_1r);});break;case 6:return new F(function(){return _2(_1a,_1r);});break;case 7:return new F(function(){return _2(_19,_1r);});break;case 8:return new F(function(){return _2(_18,_1r);});break;case 9:return new F(function(){return _2(_17,_1r);});break;case 10:return new F(function(){return _2(_1o,_1r);});break;case 11:return new F(function(){return _2(_1n,_1r);});break;case 12:return new F(function(){return _2(_1m,_1r);});break;case 13:return new F(function(){return _2(_1l,_1r);});break;case 14:return new F(function(){return _2(_1k,_1r);});break;case 15:return new F(function(){return _2(_1j,_1r);});break;case 16:return new F(function(){return _2(_1i,_1r);});break;case 17:return new F(function(){return _2(_1h,_1r);});break;default:return new F(function(){return _2(_16,_1r);});}},_1s=new T(function(){return B(unCStr("}"));}),_1t=new T(function(){return B(unCStr("{handle: "));}),_1u=function(_1v,_1w,_1x,_1y,_1z,_1A){var _1B=new T(function(){var _1C=new T(function(){var _1D=new T(function(){var _1E=E(_1y);if(!_1E._){return E(_1A);}else{var _1F=new T(function(){return B(_2(_1E,new T(function(){return B(_2(_14,_1A));},1)));},1);return B(_2(_15,_1F));}},1);return B(_1p(_1w,_1D));}),_1G=E(_1x);if(!_1G._){return E(_1C);}else{return B(_2(_1G,new T(function(){return B(_2(_13,_1C));},1)));}}),_1H=E(_1z);if(!_1H._){var _1I=E(_1v);if(!_1I._){return E(_1B);}else{var _1J=E(_1I.a);if(!_1J._){var _1K=new T(function(){var _1L=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1L));},1);return new F(function(){return _2(_1t,_1K);});}else{var _1M=new T(function(){var _1N=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1N));},1);return new F(function(){return _2(_1t,_1M);});}}}else{return new F(function(){return _2(_1H.a,new T(function(){return B(_2(_13,_1B));},1));});}},_1O=function(_1P){var _1Q=E(_1P);return new F(function(){return _1u(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_6);});},_1R=function(_1S){return new T2(0,_1T,_1S);},_1U=function(_1V,_1W,_1X){var _1Y=E(_1W);return new F(function(){return _1u(_1Y.a,_1Y.b,_1Y.c,_1Y.d,_1Y.f,_1X);});},_1Z=function(_20,_21){var _22=E(_20);return new F(function(){return _1u(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=44,_24=93,_25=91,_26=function(_27,_28,_29){var _2a=E(_28);if(!_2a._){return new F(function(){return unAppCStr("[]",_29);});}else{var _2b=new T(function(){var _2c=new T(function(){var _2d=function(_2e){var _2f=E(_2e);if(!_2f._){return E(new T2(1,_24,_29));}else{var _2g=new T(function(){return B(A2(_27,_2f.a,new T(function(){return B(_2d(_2f.b));})));});return new T2(1,_23,_2g);}};return B(_2d(_2a.b));});return B(A2(_27,_2a.a,_2c));});return new T2(1,_25,_2b);}},_2h=function(_2i,_2j){return new F(function(){return _26(_1Z,_2i,_2j);});},_2k=new T3(0,_1U,_1O,_2h),_1T=new T(function(){return new T5(0,_O,_2k,_1R,_10,_1O);}),_2l=new T(function(){return E(_1T);}),_2m=function(_2n){return E(E(_2n).c);},_2o=__Z,_2p=7,_2q=function(_2r){return new T6(0,_2o,_2p,_6,_2r,_2o,_2o);},_2s=function(_2t,_){var _2u=new T(function(){return B(A2(_2m,_2l,new T(function(){return B(A1(_2q,_2t));})));});return new F(function(){return die(_2u);});},_2v=function(_2w,_){return new F(function(){return _2s(_2w,_);});},_2x=function(_2y){return new F(function(){return A1(_2v,_2y);});},_2z=function(_2A,_2B,_){var _2C=B(A1(_2A,_));return new F(function(){return A2(_2B,_2C,_);});},_2D=new T5(0,_I,_2z,_E,_C,_2x),_2E=function(_2F){return E(_2F);},_2G=new T2(0,_2D,_2E),_2H=function(_2I){var _2J=E(_2I);return new T0(2);},_2K=function(_2L,_2M,_2N){return new T1(1,new T2(1,new T(function(){return B(A1(_2N,new T2(0,_7,_2M)));}),new T2(1,new T(function(){return B(A2(_2L,_2M,_2H));}),_6)));},_2O=function(_2P,_2Q,_2R){var _2S=new T(function(){return B(A1(_2P,_2R));}),_2T=function(_2U){var _2V=function(_2W){var _2X=E(_2W);return new F(function(){return A2(_2Q,_2X.b,function(_2Y){return new F(function(){return A1(_2U,new T2(0,_2X.a,E(_2Y).b));});});});};return new F(function(){return A1(_2S,_2V);});};return E(_2T);},_2Z=function(_30,_31,_32){var _33=new T(function(){return B(A1(_30,_32));}),_34=function(_35){var _36=function(_37){return new F(function(){return A1(_35,E(_37));});};return new F(function(){return A1(_33,function(_38){return new F(function(){return A2(_31,E(_38).b,_36);});});});};return E(_34);},_39=function(_3a,_3b,_3c){var _3d=new T(function(){return B(A1(_3a,_3c));}),_3e=function(_3f){var _3g=function(_3h){var _3i=E(_3h),_3j=function(_3k){var _3l=E(_3k);return new F(function(){return A1(_3f,new T2(0,new T(function(){return B(A1(_3i.a,_3l.a));}),_3l.b));});};return new F(function(){return A2(_3b,_3i.b,_3j);});};return new F(function(){return A1(_3d,_3g);});};return E(_3e);},_3m=function(_3n,_3o,_3p){return new F(function(){return _39(_3n,_3o,_3p);});},_3q=function(_3r,_3s,_3t){var _3u=new T(function(){return B(A1(_3s,_3t));}),_3v=function(_3w){var _3x=function(_3y){return new F(function(){return A1(_3w,new T(function(){return new T2(0,_3r,E(_3y).b);}));});};return new F(function(){return A1(_3u,_3x);});};return E(_3v);},_3z=function(_3A,_3B,_3C){var _3D=new T(function(){return B(A1(_3B,_3C));}),_3E=function(_3F){var _3G=function(_3H){var _3I=new T(function(){var _3J=E(_3H);return new T2(0,new T(function(){return B(A1(_3A,_3J.a));}),_3J.b);});return new F(function(){return A1(_3F,_3I);});};return new F(function(){return A1(_3D,_3G);});};return E(_3E);},_3K=function(_3n,_3o,_3p){return new F(function(){return _3z(_3n,_3o,_3p);});},_3L=new T2(0,_3K,_3q),_3M=function(_3N,_3O,_3P){return new F(function(){return A1(_3P,new T2(0,_3N,_3O));});},_3Q=function(_3n,_3o,_3p){return new F(function(){return _3M(_3n,_3o,_3p);});},_3R=new T5(0,_3L,_3Q,_3m,_2Z,_2O),_3S=function(_3T,_3U,_3V){var _3W=new T(function(){return B(A1(_3T,_3V));}),_3X=function(_3Y){return new F(function(){return A1(_3W,function(_3Z){return new F(function(){return A2(_3U,E(_3Z).b,_3Y);});});});};return E(_3X);},_40=function(_3n,_3o,_3p){return new F(function(){return _3S(_3n,_3o,_3p);});},_41=function(_42,_43,_44){var _45=new T(function(){return B(A1(_42,_44));}),_46=function(_47){return new F(function(){return A1(_45,function(_48){var _49=E(_48);return new F(function(){return A3(_43,_49.a,_49.b,_47);});});});};return E(_46);},_4a=function(_3n,_3o,_3p){return new F(function(){return _41(_3n,_3o,_3p);});},_4b=function(_4c,_4d){return new F(function(){return err(_4c);});},_4e=function(_3o,_3p){return new F(function(){return _4b(_3o,_3p);});},_4f=new T5(0,_3R,_4a,_40,_3Q,_4e),_4g=function(_4h,_4i,_4j){return new F(function(){return A1(_4h,function(_4k){return new F(function(){return A1(_4j,new T2(0,_4k,_4i));});});});},_4l=new T3(0,_4f,_4g,_2K),_4m=function(_){return new F(function(){return __jsNull();});},_4n=function(_4o){var _4p=B(A1(_4o,_));return E(_4p);},_4q=new T(function(){return B(_4n(_4m));}),_4r=new T(function(){return E(_4q);}),_4s=new T(function(){return eval("window.requestAnimationFrame");}),_4t=function(_4u,_4v,_4w,_4x){return function(_){var _4y=E(_4u),_4z=rMV(_4y),_4A=E(_4z);if(!_4A._){var _4B=B(A2(_4v,_4A.a,_)),_4C=function(_4D,_){var _4E=function(_){var _4F=rMV(_4y),_4G=function(_,_4H){var _4I=function(_){var _4J=__createJSFunc(2,function(_4K,_){var _4L=B(_4M(_,_));return _4r;}),_4N=__app1(E(_4s),_4J);return _7;},_4O=E(_4H);if(!_4O._){return new F(function(){return _4I(_);});}else{var _4P=B(A2(_4v,_4O.a,_));return new F(function(){return _4I(_);});}},_4Q=E(_4F);if(!_4Q._){return new F(function(){return _4G(_,new T1(1,_4Q.a));});}else{return new F(function(){return _4G(_,_2o);});}},_4M=function(_4R,_){return new F(function(){return _4E(_);});},_4S=B(_4M(_,_));return _4r;},_4T=__createJSFunc(2,E(_4C)),_4U=__app1(E(_4s),_4T);return new T(function(){return B(A1(_4x,new T2(0,_7,_4w)));});}else{var _4V=function(_4W,_){var _4X=function(_){var _4Y=rMV(_4y),_4Z=function(_,_50){var _51=function(_){var _52=__createJSFunc(2,function(_53,_){var _54=B(_55(_,_));return _4r;}),_56=__app1(E(_4s),_52);return _7;},_57=E(_50);if(!_57._){return new F(function(){return _51(_);});}else{var _58=B(A2(_4v,_57.a,_));return new F(function(){return _51(_);});}},_59=E(_4Y);if(!_59._){return new F(function(){return _4Z(_,new T1(1,_59.a));});}else{return new F(function(){return _4Z(_,_2o);});}},_55=function(_5a,_){return new F(function(){return _4X(_);});},_5b=B(_55(_,_));return _4r;},_5c=__createJSFunc(2,E(_4V)),_5d=__app1(E(_4s),_5c);return new T(function(){return B(A1(_4x,new T2(0,_7,_4w)));});}};},_5e=function(_){return _7;},_5f=function(_5g,_5h,_){return new F(function(){return _5e(_);});},_5i=false,_5j=function(_){return _5i;},_5k=function(_5l,_){return new F(function(){return _5j(_);});},_5m=function(_5n,_5o){var _5p=E(_5n),_5q=E(_5o);return (_5p.a!=_5q.a)?false:(_5p.b!=_5q.b)?false:_5p.c==_5q.c;},_5r=new T1(0,1),_5s=function(_5t,_5u){var _5v=E(_5t);if(!_5v._){var _5w=_5v.a,_5x=E(_5u);if(!_5x._){var _5y=_5x.a;return (_5w!=_5y)?(_5w>_5y)?2:0:1;}else{var _5z=I_compareInt(_5x.a,_5w);return (_5z<=0)?(_5z>=0)?1:2:0;}}else{var _5A=_5v.a,_5B=E(_5u);if(!_5B._){var _5C=I_compareInt(_5A,_5B.a);return (_5C>=0)?(_5C<=0)?1:2:0;}else{var _5D=I_compare(_5A,_5B.a);return (_5D>=0)?(_5D<=0)?1:2:0;}}},_5E=new T(function(){return B(unCStr("base"));}),_5F=new T(function(){return B(unCStr("GHC.Exception"));}),_5G=new T(function(){return B(unCStr("ArithException"));}),_5H=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_5E,_5F,_5G),_5I=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_5H,_6,_6),_5J=function(_5K){return E(_5I);},_5L=function(_5M){var _5N=E(_5M);return new F(function(){return _S(B(_Q(_5N.a)),_5J,_5N.b);});},_5O=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_5P=new T(function(){return B(unCStr("denormal"));}),_5Q=new T(function(){return B(unCStr("divide by zero"));}),_5R=new T(function(){return B(unCStr("loss of precision"));}),_5S=new T(function(){return B(unCStr("arithmetic underflow"));}),_5T=new T(function(){return B(unCStr("arithmetic overflow"));}),_5U=function(_5V,_5W){switch(E(_5V)){case 0:return new F(function(){return _2(_5T,_5W);});break;case 1:return new F(function(){return _2(_5S,_5W);});break;case 2:return new F(function(){return _2(_5R,_5W);});break;case 3:return new F(function(){return _2(_5Q,_5W);});break;case 4:return new F(function(){return _2(_5P,_5W);});break;default:return new F(function(){return _2(_5O,_5W);});}},_5X=function(_5Y){return new F(function(){return _5U(_5Y,_6);});},_5Z=function(_60,_61,_62){return new F(function(){return _5U(_61,_62);});},_63=function(_64,_65){return new F(function(){return _26(_5U,_64,_65);});},_66=new T3(0,_5Z,_5X,_63),_67=new T(function(){return new T5(0,_5J,_66,_68,_5L,_5X);}),_68=function(_69){return new T2(0,_67,_69);},_6a=3,_6b=new T(function(){return B(_68(_6a));}),_6c=new T(function(){return die(_6b);}),_6d=function(_6e,_6f){var _6g=E(_6e);return (_6g._==0)?_6g.a*Math.pow(2,_6f):I_toNumber(_6g.a)*Math.pow(2,_6f);},_6h=function(_6i,_6j){var _6k=E(_6i);if(!_6k._){var _6l=_6k.a,_6m=E(_6j);return (_6m._==0)?_6l==_6m.a:(I_compareInt(_6m.a,_6l)==0)?true:false;}else{var _6n=_6k.a,_6o=E(_6j);return (_6o._==0)?(I_compareInt(_6n,_6o.a)==0)?true:false:(I_compare(_6n,_6o.a)==0)?true:false;}},_6p=function(_6q){var _6r=E(_6q);if(!_6r._){return E(_6r.a);}else{return new F(function(){return I_toInt(_6r.a);});}},_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v._){var _6w=_6v.a,_6x=E(_6u);if(!_6x._){var _6y=_6x.a,_6z=addC(_6w,_6y);if(!E(_6z.b)){return new T1(0,_6z.a);}else{_6t=new T1(1,I_fromInt(_6w));_6u=new T1(1,I_fromInt(_6y));continue;}}else{_6t=new T1(1,I_fromInt(_6w));_6u=_6x;continue;}}else{var _6A=E(_6u);if(!_6A._){_6t=_6v;_6u=new T1(1,I_fromInt(_6A.a));continue;}else{return new T1(1,I_add(_6v.a,_6A.a));}}}},_6B=function(_6C,_6D){while(1){var _6E=E(_6C);if(!_6E._){var _6F=E(_6E.a);if(_6F==(-2147483648)){_6C=new T1(1,I_fromInt(-2147483648));continue;}else{var _6G=E(_6D);if(!_6G._){var _6H=_6G.a;return new T2(0,new T1(0,quot(_6F,_6H)),new T1(0,_6F%_6H));}else{_6C=new T1(1,I_fromInt(_6F));_6D=_6G;continue;}}}else{var _6I=E(_6D);if(!_6I._){_6C=_6E;_6D=new T1(1,I_fromInt(_6I.a));continue;}else{var _6J=I_quotRem(_6E.a,_6I.a);return new T2(0,new T1(1,_6J.a),new T1(1,_6J.b));}}}},_6K=new T1(0,0),_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O._){_6M=new T1(1,I_fromInt(_6O.a));continue;}else{return new T1(1,I_shiftLeft(_6O.a,_6N));}}},_6P=function(_6Q,_6R,_6S){if(!B(_6h(_6S,_6K))){var _6T=B(_6B(_6R,_6S)),_6U=_6T.a;switch(B(_5s(B(_6L(_6T.b,1)),_6S))){case 0:return new F(function(){return _6d(_6U,_6Q);});break;case 1:if(!(B(_6p(_6U))&1)){return new F(function(){return _6d(_6U,_6Q);});}else{return new F(function(){return _6d(B(_6s(_6U,_5r)),_6Q);});}break;default:return new F(function(){return _6d(B(_6s(_6U,_5r)),_6Q);});}}else{return E(_6c);}},_6V=function(_6W,_6X){var _6Y=E(_6W);if(!_6Y._){var _6Z=_6Y.a,_70=E(_6X);return (_70._==0)?_6Z>_70.a:I_compareInt(_70.a,_6Z)<0;}else{var _71=_6Y.a,_72=E(_6X);return (_72._==0)?I_compareInt(_71,_72.a)>0:I_compare(_71,_72.a)>0;}},_73=new T1(0,1),_74=function(_75,_76){var _77=E(_75);if(!_77._){var _78=_77.a,_79=E(_76);return (_79._==0)?_78<_79.a:I_compareInt(_79.a,_78)>0;}else{var _7a=_77.a,_7b=E(_76);return (_7b._==0)?I_compareInt(_7a,_7b.a)<0:I_compare(_7a,_7b.a)<0;}},_7c=new T(function(){return B(unCStr("base"));}),_7d=new T(function(){return B(unCStr("Control.Exception.Base"));}),_7e=new T(function(){return B(unCStr("PatternMatchFail"));}),_7f=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7c,_7d,_7e),_7g=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7f,_6,_6),_7h=function(_7i){return E(_7g);},_7j=function(_7k){var _7l=E(_7k);return new F(function(){return _S(B(_Q(_7l.a)),_7h,_7l.b);});},_7m=function(_7n){return E(E(_7n).a);},_7o=function(_7p){return new T2(0,_7q,_7p);},_7r=function(_7s,_7t){return new F(function(){return _2(E(_7s).a,_7t);});},_7u=function(_7v,_7w){return new F(function(){return _26(_7r,_7v,_7w);});},_7x=function(_7y,_7z,_7A){return new F(function(){return _2(E(_7z).a,_7A);});},_7B=new T3(0,_7x,_7m,_7u),_7q=new T(function(){return new T5(0,_7h,_7B,_7o,_7j,_7m);}),_7C=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_7D=function(_7E,_7F){return new F(function(){return die(new T(function(){return B(A2(_2m,_7F,_7E));}));});},_7G=function(_7H,_69){return new F(function(){return _7D(_7H,_69);});},_7I=function(_7J,_7K){var _7L=E(_7K);if(!_7L._){return new T2(0,_6,_6);}else{var _7M=_7L.a;if(!B(A1(_7J,_7M))){return new T2(0,_6,_7L);}else{var _7N=new T(function(){var _7O=B(_7I(_7J,_7L.b));return new T2(0,_7O.a,_7O.b);});return new T2(0,new T2(1,_7M,new T(function(){return E(E(_7N).a);})),new T(function(){return E(E(_7N).b);}));}}},_7P=32,_7Q=new T(function(){return B(unCStr("\n"));}),_7R=function(_7S){return (E(_7S)==124)?false:true;},_7T=function(_7U,_7V){var _7W=B(_7I(_7R,B(unCStr(_7U)))),_7X=_7W.a,_7Y=function(_7Z,_80){var _81=new T(function(){var _82=new T(function(){return B(_2(_7V,new T(function(){return B(_2(_80,_7Q));},1)));});return B(unAppCStr(": ",_82));},1);return new F(function(){return _2(_7Z,_81);});},_83=E(_7W.b);if(!_83._){return new F(function(){return _7Y(_7X,_6);});}else{if(E(_83.a)==124){return new F(function(){return _7Y(_7X,new T2(1,_7P,_83.b));});}else{return new F(function(){return _7Y(_7X,_6);});}}},_84=function(_85){return new F(function(){return _7G(new T1(0,new T(function(){return B(_7T(_85,_7C));})),_7q);});},_86=function(_87){var _88=function(_89,_8a){while(1){if(!B(_74(_89,_87))){if(!B(_6V(_89,_87))){if(!B(_6h(_89,_87))){return new F(function(){return _84("GHC/Integer/Type.lhs:(555,5)-(557,32)|function l2");});}else{return E(_8a);}}else{return _8a-1|0;}}else{var _8b=B(_6L(_89,1)),_8c=_8a+1|0;_89=_8b;_8a=_8c;continue;}}};return new F(function(){return _88(_73,0);});},_8d=function(_8e){var _8f=E(_8e);if(!_8f._){var _8g=_8f.a>>>0;if(!_8g){return -1;}else{var _8h=function(_8i,_8j){while(1){if(_8i>=_8g){if(_8i<=_8g){if(_8i!=_8g){return new F(function(){return _84("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_8j);}}else{return _8j-1|0;}}else{var _8k=imul(_8i,2)>>>0,_8l=_8j+1|0;_8i=_8k;_8j=_8l;continue;}}};return new F(function(){return _8h(1,0);});}}else{return new F(function(){return _86(_8f);});}},_8m=function(_8n){var _8o=E(_8n);if(!_8o._){var _8p=_8o.a>>>0;if(!_8p){return new T2(0,-1,0);}else{var _8q=function(_8r,_8s){while(1){if(_8r>=_8p){if(_8r<=_8p){if(_8r!=_8p){return new F(function(){return _84("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_8s);}}else{return _8s-1|0;}}else{var _8t=imul(_8r,2)>>>0,_8u=_8s+1|0;_8r=_8t;_8s=_8u;continue;}}};return new T2(0,B(_8q(1,0)),(_8p&_8p-1>>>0)>>>0&4294967295);}}else{var _8v=_8o.a;return new T2(0,B(_8d(_8o)),I_compareInt(I_and(_8v,I_sub(_8v,I_fromInt(1))),0));}},_8w=function(_8x,_8y){var _8z=E(_8x);if(!_8z._){var _8A=_8z.a,_8B=E(_8y);return (_8B._==0)?_8A<=_8B.a:I_compareInt(_8B.a,_8A)>=0;}else{var _8C=_8z.a,_8D=E(_8y);return (_8D._==0)?I_compareInt(_8C,_8D.a)<=0:I_compare(_8C,_8D.a)<=0;}},_8E=function(_8F,_8G){while(1){var _8H=E(_8F);if(!_8H._){var _8I=_8H.a,_8J=E(_8G);if(!_8J._){return new T1(0,(_8I>>>0&_8J.a>>>0)>>>0&4294967295);}else{_8F=new T1(1,I_fromInt(_8I));_8G=_8J;continue;}}else{var _8K=E(_8G);if(!_8K._){_8F=_8H;_8G=new T1(1,I_fromInt(_8K.a));continue;}else{return new T1(1,I_and(_8H.a,_8K.a));}}}},_8L=function(_8M,_8N){while(1){var _8O=E(_8M);if(!_8O._){var _8P=_8O.a,_8Q=E(_8N);if(!_8Q._){var _8R=_8Q.a,_8S=subC(_8P,_8R);if(!E(_8S.b)){return new T1(0,_8S.a);}else{_8M=new T1(1,I_fromInt(_8P));_8N=new T1(1,I_fromInt(_8R));continue;}}else{_8M=new T1(1,I_fromInt(_8P));_8N=_8Q;continue;}}else{var _8T=E(_8N);if(!_8T._){_8M=_8O;_8N=new T1(1,I_fromInt(_8T.a));continue;}else{return new T1(1,I_sub(_8O.a,_8T.a));}}}},_8U=new T1(0,2),_8V=function(_8W,_8X){var _8Y=E(_8W);if(!_8Y._){var _8Z=(_8Y.a>>>0&(2<<_8X>>>0)-1>>>0)>>>0,_90=1<<_8X>>>0;return (_90<=_8Z)?(_90>=_8Z)?1:2:0;}else{var _91=B(_8E(_8Y,B(_8L(B(_6L(_8U,_8X)),_73)))),_92=B(_6L(_73,_8X));return (!B(_6V(_92,_91)))?(!B(_74(_92,_91)))?1:2:0;}},_93=function(_94,_95){while(1){var _96=E(_94);if(!_96._){_94=new T1(1,I_fromInt(_96.a));continue;}else{return new T1(1,I_shiftRight(_96.a,_95));}}},_97=function(_98,_99,_9a,_9b){var _9c=B(_8m(_9b)),_9d=_9c.a;if(!E(_9c.b)){var _9e=B(_8d(_9a));if(_9e<((_9d+_98|0)-1|0)){var _9f=_9d+(_98-_99|0)|0;if(_9f>0){if(_9f>_9e){if(_9f<=(_9e+1|0)){if(!E(B(_8m(_9a)).b)){return 0;}else{return new F(function(){return _6d(_5r,_98-_99|0);});}}else{return 0;}}else{var _9g=B(_93(_9a,_9f));switch(B(_8V(_9a,_9f-1|0))){case 0:return new F(function(){return _6d(_9g,_98-_99|0);});break;case 1:if(!(B(_6p(_9g))&1)){return new F(function(){return _6d(_9g,_98-_99|0);});}else{return new F(function(){return _6d(B(_6s(_9g,_5r)),_98-_99|0);});}break;default:return new F(function(){return _6d(B(_6s(_9g,_5r)),_98-_99|0);});}}}else{return new F(function(){return _6d(_9a,(_98-_99|0)-_9f|0);});}}else{if(_9e>=_99){var _9h=B(_93(_9a,(_9e+1|0)-_99|0));switch(B(_8V(_9a,_9e-_99|0))){case 0:return new F(function(){return _6d(_9h,((_9e-_9d|0)+1|0)-_99|0);});break;case 2:return new F(function(){return _6d(B(_6s(_9h,_5r)),((_9e-_9d|0)+1|0)-_99|0);});break;default:if(!(B(_6p(_9h))&1)){return new F(function(){return _6d(_9h,((_9e-_9d|0)+1|0)-_99|0);});}else{return new F(function(){return _6d(B(_6s(_9h,_5r)),((_9e-_9d|0)+1|0)-_99|0);});}}}else{return new F(function(){return _6d(_9a, -_9d);});}}}else{var _9i=B(_8d(_9a))-_9d|0,_9j=function(_9k){var _9l=function(_9m,_9n){if(!B(_8w(B(_6L(_9n,_99)),_9m))){return new F(function(){return _6P(_9k-_99|0,_9m,_9n);});}else{return new F(function(){return _6P((_9k-_99|0)+1|0,_9m,B(_6L(_9n,1)));});}};if(_9k>=_99){if(_9k!=_99){return new F(function(){return _9l(_9a,new T(function(){return B(_6L(_9b,_9k-_99|0));}));});}else{return new F(function(){return _9l(_9a,_9b);});}}else{return new F(function(){return _9l(new T(function(){return B(_6L(_9a,_99-_9k|0));}),_9b);});}};if(_98>_9i){return new F(function(){return _9j(_98);});}else{return new F(function(){return _9j(_9i);});}}},_9o=new T1(0,2147483647),_9p=new T(function(){return B(_6s(_9o,_73));}),_9q=function(_9r){var _9s=E(_9r);if(!_9s._){var _9t=E(_9s.a);return (_9t==(-2147483648))?E(_9p):new T1(0, -_9t);}else{return new T1(1,I_negate(_9s.a));}},_9u=new T(function(){return 0/0;}),_9v=new T(function(){return -1/0;}),_9w=new T(function(){return 1/0;}),_9x=0,_9y=function(_9z,_9A){if(!B(_6h(_9A,_6K))){if(!B(_6h(_9z,_6K))){if(!B(_74(_9z,_6K))){return new F(function(){return _97(-1021,53,_9z,_9A);});}else{return  -B(_97(-1021,53,B(_9q(_9z)),_9A));}}else{return E(_9x);}}else{return (!B(_6h(_9z,_6K)))?(!B(_74(_9z,_6K)))?E(_9w):E(_9v):E(_9u);}},_9B=function(_9C){var _9D=E(_9C);return new F(function(){return _9y(_9D.a,_9D.b);});},_9E=function(_9F){return 1/E(_9F);},_9G=function(_9H){var _9I=E(_9H);return (_9I!=0)?(_9I<=0)? -_9I:E(_9I):E(_9x);},_9J=function(_9K){var _9L=E(_9K);if(!_9L._){return _9L.a;}else{return new F(function(){return I_toNumber(_9L.a);});}},_9M=function(_9N){return new F(function(){return _9J(_9N);});},_9O=1,_9P=-1,_9Q=function(_9R){var _9S=E(_9R);return (_9S<=0)?(_9S>=0)?E(_9S):E(_9P):E(_9O);},_9T=function(_9U,_9V){return E(_9U)-E(_9V);},_9W=function(_9X){return  -E(_9X);},_9Y=function(_9Z,_a0){return E(_9Z)+E(_a0);},_a1=function(_a2,_a3){return E(_a2)*E(_a3);},_a4={_:0,a:_9Y,b:_9T,c:_a1,d:_9W,e:_9G,f:_9Q,g:_9M},_a5=function(_a6,_a7){return E(_a6)/E(_a7);},_a8=new T4(0,_a4,_a5,_9E,_9B),_a9=function(_aa,_ab){return new T2(1,_aa,new T1(0,_ab));},_ac=function(_ad,_ae,_af){var _ag=E(_ae);if(!_ag._){return new F(function(){return A1(_af,_ag.a);});}else{return new T2(1,_ag.a,new T(function(){return B(_a9(_ag.b,_af));}));}},_ah=function(_ai){return new T1(0,_ai);},_aj=function(_ak){return new F(function(){return err(_ak);});},_al=function(_am){return new T5(0,_am,function(_an,_ai){return new F(function(){return _ac(_am,_an,_ai);});},function(_an,_ai){return new F(function(){return _ao(_am,_an,_ai);});},_ah,_aj);},_ap=function(_aq){return E(E(_aq).b);},_ao=function(_ar,_as,_at){return new F(function(){return A3(_ap,B(_al(_ar)),_as,function(_au){return E(_at);});});},_av=function(_aw){var _ax=new T(function(){return B(_ay(_aw));});return function(_az,_aA){return new F(function(){return _ao(_ax,_az,_aA);});};},_aB=function(_aC,_aD){var _aE=E(_aC);if(!_aE._){var _aF=E(_aD);return (_aF._==0)?E(_aE):new T2(1,_aF.a,new T2(1,_aF.b,new T1(0,function(_aG){return E(_aE);})));}else{var _aH=function(_aI){var _aJ=new T1(0,_aI),_aK=E(_aD);return (_aK._==0)?E(_aJ):new T2(1,_aK.a,new T2(1,_aK.b,new T1(0,function(_aL){return E(_aJ);})));};return new T2(1,_aE.a,new T2(1,_aE.b,new T1(0,_aH)));}},_aM=function(_aN,_aO){var _aP=function(_aQ){var _aR=E(_aO);if(!_aR._){return new T1(0,new T(function(){return B(A1(_aQ,_aR.a));}));}else{var _aS=function(_aT){return new T1(0,new T(function(){return B(A1(_aQ,_aT));}));};return new T2(1,_aR.a,new T2(1,_aR.b,new T1(0,_aS)));}},_aU=E(_aN);if(!_aU._){return new F(function(){return _aP(_aU.a);});}else{return new T2(1,_aU.a,new T2(1,_aU.b,new T1(0,_aP)));}},_ay=function(_aV){return new T5(0,_aV,_ah,_aM,new T(function(){return B(_av(_aV));}),_aB);},_aW=new T(function(){return new T2(0,_aX,_aY);}),_aZ=new T(function(){return B(_ay(_aW));}),_b0=new T(function(){return B(_al(_aZ));}),_b1=function(_b2){return E(E(_b2).d);},_b3=function(_b4,_b5,_b6){var _b7=function(_b8){return new F(function(){return A2(_b1,_b4,new T(function(){return B(A1(_b5,_b8));}));});};return new F(function(){return A3(_ap,_b4,_b6,_b7);});},_aX=function(_an,_ai){return new F(function(){return _b3(_b0,_an,_ai);});},_aY=function(_b9,_ba){return new F(function(){return _aX(function(_bb){return E(_b9);},_ba);});},_bc=function(_bd,_be,_bf){var _bg=E(_bd);return E(_be)*(1-_bg)+E(_bf)*_bg;},_bh=function(_bi,_bj){return (E(_bi)!=E(_bj))?true:false;},_bk=function(_bl,_bm){return E(_bl)==E(_bm);},_bn=new T2(0,_bk,_bh),_bo=function(_bp,_bq){return E(_bp)<E(_bq);},_br=function(_bs,_bt){return E(_bs)<=E(_bt);},_bu=function(_bv,_bw){return E(_bv)>E(_bw);},_bx=function(_by,_bz){return E(_by)>=E(_bz);},_bA=function(_bB,_bC){var _bD=E(_bB),_bE=E(_bC);return (_bD>=_bE)?(_bD!=_bE)?2:1:0;},_bF=function(_bG,_bH){var _bI=E(_bG),_bJ=E(_bH);return (_bI>_bJ)?E(_bI):E(_bJ);},_bK=function(_bL,_bM){var _bN=E(_bL),_bO=E(_bM);return (_bN>_bO)?E(_bO):E(_bN);},_bP={_:0,a:_bn,b:_bA,c:_bo,d:_br,e:_bu,f:_bx,g:_bF,h:_bK},_bQ=function(_bR){var _bS=hs_intToInt64(_bR);return E(_bS);},_bT=function(_bU){var _bV=E(_bU);if(!_bV._){return new F(function(){return _bQ(_bV.a);});}else{return new F(function(){return I_toInt64(_bV.a);});}},_bW=function(_bX){return new F(function(){return _bT(_bX);});},_bY=function(_bZ,_c0){return new F(function(){return hs_timesInt64(E(_bZ),E(_c0));});},_c1=function(_c2,_c3){return new F(function(){return hs_plusInt64(E(_c2),E(_c3));});},_c4=function(_c5,_c6){return new F(function(){return hs_minusInt64(E(_c5),E(_c6));});},_c7=function(_c8){var _c9=hs_geInt64(_c8,new Long(0,0));if(!_c9){var _ca=hs_negateInt64(_c8);return E(_ca);}else{return E(_c8);}},_cb=function(_cc){return new F(function(){return _c7(E(_cc));});},_cd=function(_ce){return new F(function(){return hs_negateInt64(E(_ce));});},_cf=function(_cg){var _ch=hs_gtInt64(_cg,new Long(0,0));if(!_ch){var _ci=hs_eqInt64(_cg,new Long(0,0));if(!_ci){return new F(function(){return new Long(4294967295,-1);});}else{return new F(function(){return new Long(0,0);});}}else{return new F(function(){return new Long(1,0);});}},_cj=function(_ck){return new F(function(){return _cf(E(_ck));});},_cl={_:0,a:_c1,b:_c4,c:_bY,d:_cd,e:_cb,f:_cj,g:_bW},_cm=true,_cn=new T1(0,0),_co=function(_cp,_cq){while(1){var _cr=E(_cp);if(!_cr._){var _cs=_cr.a,_ct=E(_cq);if(!_ct._){return new T1(0,(_cs>>>0|_ct.a>>>0)>>>0&4294967295);}else{_cp=new T1(1,I_fromInt(_cs));_cq=_ct;continue;}}else{var _cu=E(_cq);if(!_cu._){_cp=_cr;_cq=new T1(1,I_fromInt(_cu.a));continue;}else{return new T1(1,I_or(_cr.a,_cu.a));}}}},_cv=function(_cw){var _cx=E(_cw);if(!_cx._){return E(_cn);}else{return new F(function(){return _co(new T1(0,E(_cx.a)),B(_6L(B(_cv(_cx.b)),31)));});}},_cy=function(_cz,_cA){if(!E(_cz)){return new F(function(){return _9q(B(_cv(_cA)));});}else{return new F(function(){return _cv(_cA);});}},_cB=2147483647,_cC=2147483647,_cD=1,_cE=new T2(1,_cD,_6),_cF=new T2(1,_cC,_cE),_cG=new T2(1,_cB,_cF),_cH=new T(function(){return B(_cy(_cm,_cG));}),_cI=0,_cJ=0,_cK=2,_cL=new T2(1,_cK,_6),_cM=new T2(1,_cJ,_cL),_cN=new T2(1,_cI,_cM),_cO=new T(function(){return B(_cy(_5i,_cN));}),_cP=new Long(2,0),_cQ=new T(function(){return B(unCStr("Negative exponent"));}),_cR=new T(function(){return B(err(_cQ));}),_cS=new Long(1,0),_cT=new Long(4294967295,2147483647),_cU=new Long(0,-2147483648),_cV=new T2(0,_cU,_cT),_cW=new T1(0,1),_cX=function(_cY){return E(E(_cY).a);},_cZ=function(_d0){return E(E(_d0).a);},_d1=function(_d2){return E(E(_d2).g);},_d3=function(_d4){return E(E(_d4).b);},_d5=function(_d6){return E(E(_d6).i);},_d7=function(_d8,_d9,_da){var _db=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_d8));})));})));}),_dc=new T(function(){return B(_d3(_d9));}),_dd=function(_de){return (!B(_6V(_de,B(A2(_d5,_d8,_dc)))))?new T2(1,new T(function(){return B(A1(_db,_de));}),new T(function(){return B(_dd(B(_6s(_de,_cW))));})):__Z;};return new F(function(){return _dd(B(A2(_d5,_d8,_da)));});},_df=function(_dg){return new F(function(){return _d7(_dh,_cV,_dg);});},_di=new T1(0,0),_dj=function(_dk,_dl){var _dm=E(_dk);if(!_dm._){var _dn=_dm.a,_do=E(_dl);return (_do._==0)?_dn>=_do.a:I_compareInt(_do.a,_dn)<=0;}else{var _dp=_dm.a,_dq=E(_dl);return (_dq._==0)?I_compareInt(_dp,_dq.a)>=0:I_compare(_dp,_dq.a)>=0;}},_dr=function(_ds,_dt,_du,_dv,_dw){var _dx=function(_dy){if(!B(_6V(_dy,_dw))){return new F(function(){return A2(_ds,_dy,new T(function(){return B(_dx(B(_6s(_dy,_dv))));}));});}else{return E(_dt);}};return new F(function(){return _dx(_du);});},_dz=function(_dA,_dB,_dC,_dD,_dE){if(!B(_dj(_dD,_di))){var _dF=function(_dG){if(!B(_74(_dG,_dE))){return new F(function(){return A2(_dA,_dG,new T(function(){return B(_dF(B(_6s(_dG,_dD))));}));});}else{return E(_dB);}};return new F(function(){return _dF(_dC);});}else{return new F(function(){return _dr(_dA,_dB,_dC,_dD,_dE);});}},_dH=function(_dI){return E(E(_dI).a);},_dJ=function(_dK,_dL,_dM,_dN){var _dO=B(A2(_d5,_dK,_dN)),_dP=B(A2(_d5,_dK,_dM));if(!B(_dj(_dO,_dP))){var _dQ=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_dK));})));})));}),_dR=function(_dS,_dT){return new T2(1,new T(function(){return B(A1(_dQ,_dS));}),_dT);};return new F(function(){return _dz(_dR,_6,_dP,B(_8L(_dO,_dP)),B(A2(_d5,_dK,new T(function(){return B(_dH(_dL));}))));});}else{var _dU=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_dK));})));})));}),_dV=function(_dW,_dX){return new T2(1,new T(function(){return B(A1(_dU,_dW));}),_dX);};return new F(function(){return _dz(_dV,_6,_dP,B(_8L(_dO,_dP)),B(A2(_d5,_dK,new T(function(){return B(_d3(_dL));}))));});}},_dY=function(_dZ,_dg){return new F(function(){return _dJ(_dh,_cV,_dZ,_dg);});},_e0=function(_e1,_e2,_e3,_e4){var _e5=B(A2(_d5,_e1,_e2)),_e6=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_e1));})));})));}),_e7=function(_e8,_e9){return new T2(1,new T(function(){return B(A1(_e6,_e8));}),_e9);};return new F(function(){return _dz(_e7,_6,_e5,B(_8L(B(A2(_d5,_e1,_e3)),_e5)),B(A2(_d5,_e1,_e4)));});},_ea=function(_eb,_dZ,_dg){return new F(function(){return _e0(_dh,_eb,_dZ,_dg);});},_ec=function(_ed,_ee,_ef){var _eg=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_ed));})));})));}),_eh=function(_ei){return (!B(_6V(_ei,B(A2(_d5,_ed,_ef)))))?new T2(1,new T(function(){return B(A1(_eg,_ei));}),new T(function(){return B(_eh(B(_6s(_ei,_cW))));})):__Z;};return new F(function(){return _eh(B(A2(_d5,_ed,_ee)));});},_ej=function(_dZ,_dg){return new F(function(){return _ec(_dh,_dZ,_dg);});},_ek=new T(function(){return hs_intToInt64(2147483647);}),_el=function(_em){return new T1(0,_em);},_en=function(_eo){var _ep=hs_intToInt64(2147483647),_eq=hs_leInt64(_eo,_ep);if(!_eq){return new T1(1,I_fromInt64(_eo));}else{var _er=hs_intToInt64(-2147483648),_es=hs_geInt64(_eo,_er);if(!_es){return new T1(1,I_fromInt64(_eo));}else{var _et=hs_int64ToInt(_eo);return new F(function(){return _el(_et);});}}},_eu=function(_ev){return new F(function(){return _en(E(_ev));});},_ew=function(_ex){while(1){var _ey=E(_ex);if(!_ey._){_ex=new T1(1,I_fromInt(_ey.a));continue;}else{return new F(function(){return I_toString(_ey.a);});}}},_ez=function(_eA,_eB){return new F(function(){return _2(fromJSStr(B(_ew(_eA))),_eB);});},_eC=41,_eD=40,_eE=new T1(0,0),_eF=function(_eG,_eH,_eI){if(_eG<=6){return new F(function(){return _ez(_eH,_eI);});}else{if(!B(_74(_eH,_eE))){return new F(function(){return _ez(_eH,_eI);});}else{return new T2(1,_eD,new T(function(){return B(_2(fromJSStr(B(_ew(_eH))),new T2(1,_eC,_eI)));}));}}},_eJ=function(_eK){return new F(function(){return _eF(0,B(_eu(_eK)),_6);});},_eL=function(_eM,_eN){return new F(function(){return _eF(0,B(_en(E(_eM))),_eN);});},_eO=function(_eP,_eQ){return new F(function(){return _26(_eL,_eP,_eQ);});},_eR=function(_eS,_eT){var _eU=new T(function(){return B(_en(E(_eT)));});return function(_eV){return new F(function(){return _eF(E(_eS),_eU,_eV);});};},_eW=new T3(0,_eR,_eJ,_eO),_eX=new T2(1,_eC,_6),_eY=function(_eZ,_f0,_f1){return new F(function(){return A1(_eZ,new T2(1,_23,new T(function(){return B(A1(_f0,_f1));})));});},_f2=new T(function(){return B(unCStr(": empty list"));}),_f3=new T(function(){return B(unCStr("Prelude."));}),_f4=function(_f5){return new F(function(){return err(B(_2(_f3,new T(function(){return B(_2(_f5,_f2));},1))));});},_f6=new T(function(){return B(unCStr("foldr1"));}),_f7=new T(function(){return B(_f4(_f6));}),_f8=function(_f9,_fa){var _fb=E(_fa);if(!_fb._){return E(_f7);}else{var _fc=_fb.a,_fd=E(_fb.b);if(!_fd._){return E(_fc);}else{return new F(function(){return A2(_f9,_fc,new T(function(){return B(_f8(_f9,_fd));}));});}}},_fe=function(_ff,_fg){var _fh=jsShowI(_ff);return new F(function(){return _2(fromJSStr(_fh),_fg);});},_fi=function(_fj,_fk,_fl){if(_fk>=0){return new F(function(){return _fe(_fk,_fl);});}else{if(_fj<=6){return new F(function(){return _fe(_fk,_fl);});}else{return new T2(1,_eD,new T(function(){var _fm=jsShowI(_fk);return B(_2(fromJSStr(_fm),new T2(1,_eC,_fl)));}));}}},_fn=function(_fo){return new F(function(){return _fi(0,-2147483648,_fo);});},_fp=function(_fq){return new F(function(){return _fi(0,2147483647,_fq);});},_fr=new T2(1,_fp,_6),_fs=new T2(1,_fn,_fr),_ft=new T(function(){return B(_f8(_eY,_fs));}),_fu=new T(function(){return B(A1(_ft,_eX));}),_fv=new T2(1,_eD,_fu),_fw=new T(function(){return B(unAppCStr(") is outside of Int\'s bounds ",_fv));}),_fx=function(_fy){return E(E(_fy).b);},_fz=function(_fA,_fB,_fC){var _fD=new T(function(){var _fE=new T(function(){return B(unAppCStr("}: value (",new T(function(){return B(_2(B(A2(_fx,_fC,_fB)),_fw));})));},1);return B(_2(_fA,_fE));});return new F(function(){return err(B(unAppCStr("Enum.fromEnum{",_fD)));});},_fF=function(_fG,_fH,_fI){return new F(function(){return _fz(_fH,_fI,_fG);});},_fJ=new T(function(){return B(unCStr("Int64"));}),_fK=function(_fL){return new F(function(){return _fF(_eW,_fJ,_fL);});},_fM=function(_fN){return new F(function(){return _fK(_fN);});},_fO=new T(function(){return hs_intToInt64(-2147483648);}),_fP=function(_fQ){var _fR=hs_geInt64(_fQ,E(_fO));if(!_fR){return new F(function(){return _fM(_fQ);});}else{var _fS=hs_leInt64(_fQ,E(_ek));if(!_fS){return new F(function(){return _fM(_fQ);});}else{var _fT=hs_int64ToInt(_fQ);return E(_fT);}}},_fU=function(_fV){return new F(function(){return _fP(E(_fV));});},_fW=new T(function(){return B(unCStr("}: tried to take `pred\' of minBound"));}),_fX=function(_fY){return new F(function(){return err(B(unAppCStr("Enum.pred{",new T(function(){return B(_2(_fY,_fW));}))));});},_fZ=function(_g0){return new F(function(){return _fX(_g0);});},_g1=new T(function(){return B(_fZ(_fJ));}),_g2=function(_g3){var _g4=hs_neInt64(_g3,new Long(0,-2147483648));if(!_g4){return E(_g1);}else{var _g5=hs_minusInt64(_g3,new Long(1,0));return E(_g5);}},_g6=function(_g7){return new F(function(){return _g2(E(_g7));});},_g8=new T(function(){return B(unCStr("}: tried to take `succ\' of maxBound"));}),_g9=function(_ga){return new F(function(){return err(B(unAppCStr("Enum.succ{",new T(function(){return B(_2(_ga,_g8));}))));});},_gb=function(_g0){return new F(function(){return _g9(_g0);});},_gc=new T(function(){return B(_gb(_fJ));}),_gd=function(_ge){var _gf=hs_neInt64(_ge,new Long(4294967295,2147483647));if(!_gf){return E(_gc);}else{var _gg=hs_plusInt64(_ge,new Long(1,0));return E(_gg);}},_gh=function(_gi){return new F(function(){return _gd(E(_gi));});},_gj=function(_gk){return new F(function(){return hs_intToInt64(E(_gk));});},_gl=new T(function(){return {_:0,a:_gh,b:_g6,c:_gj,d:_fU,e:_df,f:_dY,g:_ej,h:_ea};}),_gm=function(_gn,_go){var _gp=hs_minusInt64(_gn,_go);return E(_gp);},_gq=function(_gr,_gs){var _gt=hs_quotInt64(_gr,_gs);return E(_gt);},_gu=function(_gv,_gw){var _gx=hs_intToInt64(1),_gy=_gx,_gz=hs_intToInt64(0),_gA=_gz,_gB=hs_gtInt64(_gv,_gA),_gC=function(_gD){var _gE=hs_ltInt64(_gv,_gA);if(!_gE){return new F(function(){return _gq(_gv,_gw);});}else{var _gF=hs_gtInt64(_gw,_gA);if(!_gF){return new F(function(){return _gq(_gv,_gw);});}else{var _gG=hs_plusInt64(_gv,_gy),_gH=hs_quotInt64(_gG,_gw);return new F(function(){return _gm(_gH,_gy);});}}};if(!_gB){return new F(function(){return _gC(_);});}else{var _gI=hs_ltInt64(_gw,_gA);if(!_gI){return new F(function(){return _gC(_);});}else{var _gJ=hs_minusInt64(_gv,_gy),_gK=hs_quotInt64(_gJ,_gw);return new F(function(){return _gm(_gK,_gy);});}}},_gL=0,_gM=new T(function(){return B(_68(_gL));}),_gN=new T(function(){return die(_gM);}),_gO=function(_gP,_gQ){var _gR=hs_eqInt64(_gQ,new Long(0,0));if(!_gR){var _gS=hs_eqInt64(_gQ,new Long(4294967295,-1));if(!_gS){return new F(function(){return _gu(_gP,_gQ);});}else{var _gT=hs_eqInt64(_gP,new Long(0,-2147483648));if(!_gT){return new F(function(){return _gu(_gP,_gQ);});}else{return E(_gN);}}}else{return E(_6c);}},_gU=function(_gV,_gW){return new F(function(){return _gO(E(_gV),E(_gW));});},_gX=new Long(0,0),_gY=function(_gZ,_h0){var _h1=hs_plusInt64(_gZ,_h0);return E(_h1);},_h2=function(_h3,_h4){var _h5=hs_remInt64(_h3,_h4),_h6=_h5,_h7=hs_intToInt64(0),_h8=_h7,_h9=hs_gtInt64(_h3,_h8),_ha=function(_hb){var _hc=hs_neInt64(_h6,_h8);if(!_hc){return E(_h8);}else{return new F(function(){return _gY(_h6,_h4);});}},_hd=function(_he){var _hf=hs_ltInt64(_h3,_h8);if(!_hf){return E(_h6);}else{var _hg=hs_gtInt64(_h4,_h8);if(!_hg){return E(_h6);}else{return new F(function(){return _ha(_);});}}};if(!_h9){return new F(function(){return _hd(_);});}else{var _hh=hs_ltInt64(_h4,_h8);if(!_hh){return new F(function(){return _hd(_);});}else{return new F(function(){return _ha(_);});}}},_hi=function(_hj,_hk){var _hl=hs_eqInt64(_hk,new Long(0,0));if(!_hl){var _hm=hs_eqInt64(_hk,new Long(4294967295,-1));if(!_hm){return new T2(0,new T(function(){return B(_gu(_hj,_hk));}),new T(function(){return B(_h2(_hj,_hk));}));}else{var _hn=hs_eqInt64(_hj,new Long(0,-2147483648));return (!_hn)?new T2(0,new T(function(){return B(_gu(_hj,_hk));}),new T(function(){return B(_h2(_hj,_hk));})):new T2(0,_gN,_gX);}}else{return E(_6c);}},_ho=function(_hp,_hq){var _hr=B(_hi(E(_hp),E(_hq)));return new T2(0,_hr.a,_hr.b);},_hs=function(_ht,_hu){var _hv=hs_eqInt64(_hu,new Long(0,0));if(!_hv){var _hw=hs_eqInt64(_hu,new Long(4294967295,-1));if(!_hw){return new F(function(){return _h2(_ht,_hu);});}else{return new F(function(){return new Long(0,0);});}}else{return E(_6c);}},_hx=function(_hy,_hz){return new F(function(){return _hs(E(_hy),E(_hz));});},_hA=function(_hB,_hC){var _hD=hs_eqInt64(_hC,new Long(0,0));if(!_hD){var _hE=hs_eqInt64(_hC,new Long(4294967295,-1));if(!_hE){var _hF=hs_quotInt64(_hB,_hC);return E(_hF);}else{var _hG=hs_eqInt64(_hB,new Long(0,-2147483648));if(!_hG){var _hH=hs_quotInt64(_hB,_hC);return E(_hH);}else{return E(_gN);}}}else{return E(_6c);}},_hI=function(_hJ,_hK){return new F(function(){return _hA(E(_hJ),E(_hK));});},_hL=function(_hM,_hN){var _hO=hs_eqInt64(_hN,new Long(0,0));if(!_hO){var _hP=hs_eqInt64(_hN,new Long(4294967295,-1));if(!_hP){return new T2(0,new T(function(){return hs_quotInt64(_hM,_hN);}),new T(function(){return hs_remInt64(_hM,_hN);}));}else{var _hQ=hs_eqInt64(_hM,new Long(0,-2147483648));return (!_hQ)?new T2(0,new T(function(){return hs_quotInt64(_hM,_hN);}),new T(function(){return hs_remInt64(_hM,_hN);})):new T2(0,_gN,_gX);}}else{return E(_6c);}},_hR=function(_hS,_hT){var _hU=B(_hL(E(_hS),E(_hT)));return new T2(0,_hU.a,_hU.b);},_hV=function(_hW,_hX){var _hY=hs_eqInt64(_hX,new Long(0,0));if(!_hY){var _hZ=hs_eqInt64(_hX,new Long(4294967295,-1));if(!_hZ){var _i0=hs_remInt64(_hW,_hX);return E(_i0);}else{return new F(function(){return new Long(0,0);});}}else{return E(_6c);}},_i1=function(_i2,_i3){return new F(function(){return _hV(E(_i2),E(_i3));});},_i4=function(_i5,_i6){return new F(function(){return hs_neInt64(E(_i5),E(_i6));});},_i7=function(_i8,_i9){return new F(function(){return hs_eqInt64(E(_i8),E(_i9));});},_ia=new T2(0,_i7,_i4),_ib=function(_ic,_id){return new F(function(){return hs_ltInt64(E(_ic),E(_id));});},_ie=function(_if,_ig){return new F(function(){return hs_leInt64(E(_if),E(_ig));});},_ih=function(_ii,_ij){return new F(function(){return hs_gtInt64(E(_ii),E(_ij));});},_ik=function(_il,_im){return new F(function(){return hs_geInt64(E(_il),E(_im));});},_in=function(_io,_ip){var _iq=hs_eqInt64(_io,_ip);if(!_iq){var _ir=hs_leInt64(_io,_ip);return (!_ir)?2:0;}else{return 1;}},_is=function(_it,_iu){return new F(function(){return _in(E(_it),E(_iu));});},_iv=function(_iw,_ix){var _iy=E(_iw),_iz=E(_ix),_iA=hs_leInt64(_iy,_iz);return (!_iA)?E(_iy):E(_iz);},_iB=function(_iC,_iD){var _iE=E(_iC),_iF=E(_iD),_iG=hs_leInt64(_iE,_iF);return (!_iG)?E(_iF):E(_iE);},_iH={_:0,a:_ia,b:_is,c:_ib,d:_ie,e:_ih,f:_ik,g:_iv,h:_iB},_iI=new T1(0,1),_iJ=new T1(0,0),_iK=function(_iL,_iM){while(1){var _iN=E(_iL);if(!_iN._){var _iO=E(_iN.a);if(_iO==(-2147483648)){_iL=new T1(1,I_fromInt(-2147483648));continue;}else{var _iP=E(_iM);if(!_iP._){return new T1(0,_iO%_iP.a);}else{_iL=new T1(1,I_fromInt(_iO));_iM=_iP;continue;}}}else{var _iQ=_iN.a,_iR=E(_iM);return (_iR._==0)?new T1(1,I_rem(_iQ,I_fromInt(_iR.a))):new T1(1,I_rem(_iQ,_iR.a));}}},_iS=function(_iT,_iU){if(!B(_6h(_iU,_iJ))){return new F(function(){return _iK(_iT,_iU);});}else{return E(_6c);}},_iV=function(_iW,_iX){while(1){if(!B(_6h(_iX,_iJ))){var _iY=_iX,_iZ=B(_iS(_iW,_iX));_iW=_iY;_iX=_iZ;continue;}else{return E(_iW);}}},_j0=function(_j1){var _j2=E(_j1);if(!_j2._){var _j3=E(_j2.a);return (_j3==(-2147483648))?E(_9p):(_j3<0)?new T1(0, -_j3):E(_j2);}else{var _j4=_j2.a;return (I_compareInt(_j4,0)>=0)?E(_j2):new T1(1,I_negate(_j4));}},_j5=function(_j6,_j7){while(1){var _j8=E(_j6);if(!_j8._){var _j9=E(_j8.a);if(_j9==(-2147483648)){_j6=new T1(1,I_fromInt(-2147483648));continue;}else{var _ja=E(_j7);if(!_ja._){return new T1(0,quot(_j9,_ja.a));}else{_j6=new T1(1,I_fromInt(_j9));_j7=_ja;continue;}}}else{var _jb=_j8.a,_jc=E(_j7);return (_jc._==0)?new T1(0,I_toInt(I_quot(_jb,I_fromInt(_jc.a)))):new T1(1,I_quot(_jb,_jc.a));}}},_jd=5,_je=new T(function(){return B(_68(_jd));}),_jf=new T(function(){return die(_je);}),_jg=function(_jh,_ji){if(!B(_6h(_ji,_iJ))){var _jj=B(_iV(B(_j0(_jh)),B(_j0(_ji))));return (!B(_6h(_jj,_iJ)))?new T2(0,B(_j5(_jh,_jj)),B(_j5(_ji,_jj))):E(_6c);}else{return E(_jf);}},_jk=function(_jl,_jm){while(1){var _jn=E(_jl);if(!_jn._){var _jo=_jn.a,_jp=E(_jm);if(!_jp._){var _jq=_jp.a;if(!(imul(_jo,_jq)|0)){return new T1(0,imul(_jo,_jq)|0);}else{_jl=new T1(1,I_fromInt(_jo));_jm=new T1(1,I_fromInt(_jq));continue;}}else{_jl=new T1(1,I_fromInt(_jo));_jm=_jp;continue;}}else{var _jr=E(_jm);if(!_jr._){_jl=_jn;_jm=new T1(1,I_fromInt(_jr.a));continue;}else{return new T1(1,I_mul(_jn.a,_jr.a));}}}},_js=function(_jt){var _ju=B(_jg(B(_jk(B(_en(E(_jt))),_iI)),_iI));return new T2(0,E(_ju.a),E(_ju.b));},_jv=new T3(0,_cl,_iH,_js),_dh=new T(function(){return {_:0,a:_jv,b:_gl,c:_hI,d:_i1,e:_gU,f:_hx,g:_hR,h:_ho,i:_eu};}),_jw=function(_jx){return E(E(_jx).a);},_jy=function(_jz){return E(E(_jz).b);},_jA=function(_jB){return E(E(_jB).a);},_jC=new T1(0,2),_jD=function(_jE){return E(E(_jE).d);},_jF=function(_jG,_jH){var _jI=B(_cX(_jG)),_jJ=new T(function(){return B(_cZ(_jI));}),_jK=new T(function(){return B(A3(_jD,_jG,_jH,new T(function(){return B(A2(_d1,_jJ,_jC));})));});return new F(function(){return A3(_jA,B(_jw(B(_jy(_jI)))),_jK,new T(function(){return B(A2(_d1,_jJ,_iJ));}));});},_jL=function(_jM,_jN,_jO){while(1){var _jP=B((function(_jQ,_jR,_jS){if(!B(_jF(_dh,_jR))){var _jT=hs_eqInt64(_jR,new Long(1,0));if(!_jT){var _jU=hs_minusInt64(_jR,new Long(1,0));_jM=new T(function(){return B(_bY(_jQ,_jQ));});_jN=B(_hA(_jU,new Long(2,0)));_jO=new T(function(){return B(_bY(_jQ,_jS));},1);return __continue;}else{var _jV=hs_timesInt64(E(_jQ),E(_jS));return E(_jV);}}else{var _jW=B(_hA(_jR,new Long(2,0))),_jX=_jS;_jM=new T(function(){return B(_bY(_jQ,_jQ));});_jN=_jW;_jO=_jX;return __continue;}})(_jM,_jN,_jO));if(_jP!=__continue){return _jP;}}},_jY=function(_jZ,_k0){while(1){var _k1=B((function(_k2,_k3){if(!B(_jF(_dh,_k3))){var _k4=hs_eqInt64(_k3,new Long(1,0));if(!_k4){var _k5=hs_minusInt64(_k3,new Long(1,0));return new F(function(){return _jL(new T(function(){return B(_bY(_k2,_k2));}),B(_hA(_k5,new Long(2,0))),_k2);});}else{return E(_k2);}}else{var _k6=B(_hA(_k3,new Long(2,0)));_jZ=new T(function(){return B(_bY(_k2,_k2));});_k0=_k6;return __continue;}})(_jZ,_k0));if(_k1!=__continue){return _k1;}}},_k7=function(_k8,_k9){var _ka=hs_ltInt64(_k9,new Long(0,0));if(!_ka){var _kb=hs_eqInt64(_k9,new Long(0,0));if(!_kb){return new F(function(){return _jY(_k8,_k9);});}else{return E(_cS);}}else{return E(_cR);}},_kc=new T(function(){return B(_k7(_cP,new Long(53,0)));}),_kd=new T(function(){return B(_9J(B(_en(E(_kc)))));}),_ke=new T(function(){return hs_minusInt64(E(_kc),new Long(1,0));}),_kf=function(_kg,_kh){var _ki=hs_int64ToWord64(_kh),_kj=hs_int64ToWord64(_kg),_kk=hs_and64(_kj,_ki),_kl=hs_word64ToInt64(_kk);return E(_kl);},_km=new T1(0,1),_kn=function(_ko,_kp){return new T2(0,E(_ko),E(_kp));},_kq=function(_kr,_ks){var _kt=quot(_ks,52774),_ku=(imul(40692,_ks-(imul(_kt,52774)|0)|0)|0)-(imul(_kt,3791)|0)|0,_kv=new T(function(){if(_ku>=0){return _ku;}else{return _ku+2147483399|0;}}),_kw=quot(_kr,53668),_kx=(imul(40014,_kr-(imul(_kw,53668)|0)|0)|0)-(imul(_kw,12211)|0)|0,_ky=new T(function(){if(_kx>=0){return _kx;}else{return _kx+2147483563|0;}});return new T2(0,new T(function(){var _kz=E(_ky)-E(_kv)|0;if(_kz>=1){return _kz;}else{return _kz+2147483562|0;}}),new T(function(){return B(_kn(_ky,_kv));}));},_kA=new T1(0,2147483562),_kB=new T1(0,0),_kC=new T1(0,1000),_kD=function(_kE,_kF){var _kG=_kE%_kF;if(_kE<=0){if(_kE>=0){return E(_kG);}else{if(_kF<=0){return E(_kG);}else{var _kH=E(_kG);return (_kH==0)?0:_kH+_kF|0;}}}else{if(_kF>=0){if(_kE>=0){return E(_kG);}else{if(_kF<=0){return E(_kG);}else{var _kI=E(_kG);return (_kI==0)?0:_kI+_kF|0;}}}else{var _kJ=E(_kG);return (_kJ==0)?0:_kJ+_kF|0;}}},_kK=function(_kL,_kM){while(1){var _kN=E(_kL);if(!_kN._){var _kO=E(_kN.a);if(_kO==(-2147483648)){_kL=new T1(1,I_fromInt(-2147483648));continue;}else{var _kP=E(_kM);if(!_kP._){return new T1(0,B(_kD(_kO,_kP.a)));}else{_kL=new T1(1,I_fromInt(_kO));_kM=_kP;continue;}}}else{var _kQ=_kN.a,_kR=E(_kM);return (_kR._==0)?new T1(1,I_mod(_kQ,I_fromInt(_kR.a))):new T1(1,I_mod(_kQ,_kR.a));}}},_kS=function(_kT,_kU,_kV,_kW){while(1){var _kX=B((function(_kY,_kZ,_l0,_l1){if(!B(_6V(_kZ,_l0))){var _l2=B(_6s(B(_8L(_l0,_kZ)),_km)),_l3=function(_l4,_l5,_l6){while(1){if(!B(_dj(_l4,B(_jk(_l2,_kC))))){var _l7=E(_l6),_l8=B(_kq(_l7.a,_l7.b)),_l9=B(_jk(_l4,_kA)),_la=B(_6s(B(_jk(_l5,_kA)),B(_8L(B(_el(E(_l8.a))),_km))));_l4=_l9;_l5=_la;_l6=_l8.b;continue;}else{return new T2(0,_l5,_l6);}}},_lb=B(_l3(_km,_kB,_l1)),_lc=new T(function(){return B(A2(_d1,_kY,new T(function(){if(!B(_6h(_l2,_kB))){return B(_6s(_kZ,B(_kK(_lb.a,_l2))));}else{return E(_6c);}})));});return new T2(0,_lc,_lb.b);}else{var _ld=_kY,_le=_l0,_lf=_kZ,_lg=_l1;_kT=_ld;_kU=_le;_kV=_lf;_kW=_lg;return __continue;}})(_kT,_kU,_kV,_kW));if(_kX!=__continue){return _kX;}}},_lh=function(_li){var _lj=B(_kS(_cl,_cO,_cH,_li));return new T2(0,new T(function(){return B(_9J(B(_en(B(_kf(E(_ke),E(_lj.a)))))))/E(_kd);}),_lj.b);},_lk=function(_ll,_lm,_ln){while(1){var _lo=B((function(_lp,_lq,_lr){if(_lp<=_lq){var _ls=new T(function(){var _lt=B(_lh(_lr));return new T2(0,_lt.a,_lt.b);});return new T2(0,new T(function(){var _lu=E(E(_ls).a);return 0.5*_lp+_lu*(0.5*_lq-0.5*_lp)+0.5*_lp+_lu*(0.5*_lq-0.5*_lp);}),new T(function(){return E(E(_ls).b);}));}else{var _lv=_lq,_lw=_lp,_lx=_lr;_ll=_lv;_lm=_lw;_ln=_lx;return __continue;}})(_ll,_lm,_ln));if(_lo!=__continue){return _lo;}}},_ly=1420103680,_lz=465,_lA=new T2(1,_lz,_6),_lB=new T2(1,_ly,_lA),_lC=new T(function(){return B(_cy(_cm,_lB));}),_lD=0,_lE=function(_lF,_lG){var _lH=E(_lG);if(!_lH){return E(_6c);}else{var _lI=function(_lJ){if(_lF<=0){if(_lF>=0){var _lK=quotRemI(_lF,_lH);return new T2(0,_lK.a,_lK.b);}else{if(_lH<=0){var _lL=quotRemI(_lF,_lH);return new T2(0,_lL.a,_lL.b);}else{var _lM=quotRemI(_lF+1|0,_lH);return new T2(0,_lM.a-1|0,(_lM.b+_lH|0)-1|0);}}}else{if(_lH>=0){if(_lF>=0){var _lN=quotRemI(_lF,_lH);return new T2(0,_lN.a,_lN.b);}else{if(_lH<=0){var _lO=quotRemI(_lF,_lH);return new T2(0,_lO.a,_lO.b);}else{var _lP=quotRemI(_lF+1|0,_lH);return new T2(0,_lP.a-1|0,(_lP.b+_lH|0)-1|0);}}}else{var _lQ=quotRemI(_lF-1|0,_lH);return new T2(0,_lQ.a-1|0,(_lQ.b+_lH|0)+1|0);}}};if(E(_lH)==(-1)){if(E(_lF)==(-2147483648)){return new T2(0,_gN,_lD);}else{return new F(function(){return _lI(_);});}}else{return new F(function(){return _lI(_);});}}},_lR=new T1(0,-1),_lS=function(_lT){var _lU=E(_lT);if(!_lU._){var _lV=_lU.a;return (_lV>=0)?(E(_lV)==0)?E(_cn):E(_73):E(_lR);}else{var _lW=I_compareInt(_lU.a,0);return (_lW<=0)?(E(_lW)==0)?E(_cn):E(_lR):E(_73);}},_lX=function(_lY,_lZ,_m0,_m1){var _m2=B(_jk(_lZ,_m0));return new F(function(){return _jg(B(_jk(B(_jk(_lY,_m1)),B(_lS(_m2)))),B(_j0(_m2)));});},_m3=function(_m4){return E(_lC);},_m5=new T1(0,1),_m6=function(_m7,_m8){var _m9=E(_m7);return new T2(0,_m9,new T(function(){var _ma=B(_m6(B(_6s(_m9,_m8)),_m8));return new T2(1,_ma.a,_ma.b);}));},_mb=function(_mc){var _md=B(_m6(_mc,_m5));return new T2(1,_md.a,_md.b);},_me=function(_mf,_mg){var _mh=B(_m6(_mf,new T(function(){return B(_8L(_mg,_mf));})));return new T2(1,_mh.a,_mh.b);},_mi=function(_mj,_mk,_ml){if(!B(_dj(_mk,_di))){var _mm=function(_mn){return (!B(_74(_mn,_ml)))?new T2(1,_mn,new T(function(){return B(_mm(B(_6s(_mn,_mk))));})):__Z;};return new F(function(){return _mm(_mj);});}else{var _mo=function(_mp){return (!B(_6V(_mp,_ml)))?new T2(1,_mp,new T(function(){return B(_mo(B(_6s(_mp,_mk))));})):__Z;};return new F(function(){return _mo(_mj);});}},_mq=function(_mr,_ms,_mt){return new F(function(){return _mi(_mr,B(_8L(_ms,_mr)),_mt);});},_mu=function(_mv,_mw){return new F(function(){return _mi(_mv,_m5,_mw);});},_mx=function(_my){return new F(function(){return _6p(_my);});},_mz=function(_mA){return new F(function(){return _8L(_mA,_m5);});},_mB=function(_mC){return new F(function(){return _6s(_mC,_m5);});},_mD=function(_mE){return new F(function(){return _el(E(_mE));});},_mF={_:0,a:_mB,b:_mz,c:_mD,d:_mx,e:_mb,f:_me,g:_mu,h:_mq},_mG=function(_mH,_mI){if(_mH<=0){if(_mH>=0){return new F(function(){return quot(_mH,_mI);});}else{if(_mI<=0){return new F(function(){return quot(_mH,_mI);});}else{return quot(_mH+1|0,_mI)-1|0;}}}else{if(_mI>=0){if(_mH>=0){return new F(function(){return quot(_mH,_mI);});}else{if(_mI<=0){return new F(function(){return quot(_mH,_mI);});}else{return quot(_mH+1|0,_mI)-1|0;}}}else{return quot(_mH-1|0,_mI)-1|0;}}},_mJ=function(_mK,_mL){while(1){var _mM=E(_mK);if(!_mM._){var _mN=E(_mM.a);if(_mN==(-2147483648)){_mK=new T1(1,I_fromInt(-2147483648));continue;}else{var _mO=E(_mL);if(!_mO._){return new T1(0,B(_mG(_mN,_mO.a)));}else{_mK=new T1(1,I_fromInt(_mN));_mL=_mO;continue;}}}else{var _mP=_mM.a,_mQ=E(_mL);return (_mQ._==0)?new T1(1,I_div(_mP,I_fromInt(_mQ.a))):new T1(1,I_div(_mP,_mQ.a));}}},_mR=function(_mS,_mT){if(!B(_6h(_mT,_iJ))){return new F(function(){return _mJ(_mS,_mT);});}else{return E(_6c);}},_mU=function(_mV,_mW){while(1){var _mX=E(_mV);if(!_mX._){var _mY=E(_mX.a);if(_mY==(-2147483648)){_mV=new T1(1,I_fromInt(-2147483648));continue;}else{var _mZ=E(_mW);if(!_mZ._){var _n0=_mZ.a;return new T2(0,new T1(0,B(_mG(_mY,_n0))),new T1(0,B(_kD(_mY,_n0))));}else{_mV=new T1(1,I_fromInt(_mY));_mW=_mZ;continue;}}}else{var _n1=E(_mW);if(!_n1._){_mV=_mX;_mW=new T1(1,I_fromInt(_n1.a));continue;}else{var _n2=I_divMod(_mX.a,_n1.a);return new T2(0,new T1(1,_n2.a),new T1(1,_n2.b));}}}},_n3=function(_n4,_n5){if(!B(_6h(_n5,_iJ))){var _n6=B(_mU(_n4,_n5));return new T2(0,_n6.a,_n6.b);}else{return E(_6c);}},_n7=function(_n8,_n9){if(!B(_6h(_n9,_iJ))){return new F(function(){return _kK(_n8,_n9);});}else{return E(_6c);}},_na=function(_nb,_nc){if(!B(_6h(_nc,_iJ))){return new F(function(){return _j5(_nb,_nc);});}else{return E(_6c);}},_nd=function(_ne,_nf){if(!B(_6h(_nf,_iJ))){var _ng=B(_6B(_ne,_nf));return new T2(0,_ng.a,_ng.b);}else{return E(_6c);}},_nh=function(_ni){return E(_ni);},_nj=function(_nk){return E(_nk);},_nl={_:0,a:_6s,b:_8L,c:_jk,d:_9q,e:_j0,f:_lS,g:_nj},_nm=function(_nn,_no){var _np=E(_nn);if(!_np._){var _nq=_np.a,_nr=E(_no);return (_nr._==0)?_nq!=_nr.a:(I_compareInt(_nr.a,_nq)==0)?false:true;}else{var _ns=_np.a,_nt=E(_no);return (_nt._==0)?(I_compareInt(_ns,_nt.a)==0)?false:true:(I_compare(_ns,_nt.a)==0)?false:true;}},_nu=new T2(0,_6h,_nm),_nv=function(_nw,_nx){return (!B(_8w(_nw,_nx)))?E(_nw):E(_nx);},_ny=function(_nz,_nA){return (!B(_8w(_nz,_nA)))?E(_nA):E(_nz);},_nB={_:0,a:_nu,b:_5s,c:_74,d:_8w,e:_6V,f:_dj,g:_nv,h:_ny},_nC=function(_nD){return new T2(0,E(_nD),E(_cW));},_nE=new T3(0,_nl,_nB,_nC),_nF={_:0,a:_nE,b:_mF,c:_na,d:_iS,e:_mR,f:_n7,g:_nd,h:_n3,i:_nh},_nG=new T1(0,0),_nH=function(_nI,_nJ,_nK){var _nL=B(A1(_nI,_nJ));if(!B(_6h(_nL,_nG))){return new F(function(){return _mJ(B(_jk(_nJ,_nK)),_nL);});}else{return E(_6c);}},_nM=function(_nN,_nO,_nP){var _nQ=new T(function(){if(!B(_6h(_nP,_iJ))){var _nR=B(_6B(_nO,_nP));return new T2(0,_nR.a,_nR.b);}else{return E(_6c);}}),_nS=new T(function(){return B(A2(_d1,B(_cZ(B(_cX(_nN)))),new T(function(){return E(E(_nQ).a);})));});return new T2(0,_nS,new T(function(){return new T2(0,E(E(_nQ).b),E(_nP));}));},_nT=function(_nU){return E(E(_nU).b);},_nV=function(_nW,_nX,_nY){var _nZ=B(_nM(_nW,_nX,_nY)),_o0=_nZ.a,_o1=E(_nZ.b);if(!B(_74(B(_jk(_o1.a,_cW)),B(_jk(_iJ,_o1.b))))){return E(_o0);}else{var _o2=B(_cZ(B(_cX(_nW))));return new F(function(){return A3(_nT,_o2,_o0,new T(function(){return B(A2(_d1,_o2,_cW));}));});}},_o3=479723520,_o4=40233135,_o5=new T2(1,_o4,_6),_o6=new T2(1,_o3,_o5),_o7=new T(function(){return B(_cy(_cm,_o6));}),_o8=new T1(0,40587),_o9=function(_oa){var _ob=new T(function(){var _oc=B(_lX(_oa,_cW,_lC,_cW)),_od=B(_lX(_o7,_cW,_lC,_cW)),_oe=B(_lX(_oc.a,_oc.b,_od.a,_od.b));return B(_nV(_nF,_oe.a,_oe.b));});return new T2(0,new T(function(){return B(_6s(_o8,_ob));}),new T(function(){return B(_8L(_oa,B(_nH(_m3,B(_jk(_ob,_lC)),_o7))));}));},_of=new T1(0,0),_og=function(_oh,_){var _oi=__get(_oh,0),_oj=__get(_oh,1),_ok=Number(_oi),_ol=jsTrunc(_ok),_om=Number(_oj),_on=jsTrunc(_om);return new T2(0,_ol,_on);},_oo=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_op=660865024,_oq=465661287,_or=new T2(1,_oq,_6),_os=new T2(1,_op,_or),_ot=new T(function(){return B(_cy(_cm,_os));}),_ou=function(_){var _ov=__app0(E(_oo)),_ow=B(_og(_ov,_));return new T(function(){var _ox=E(_ow);if(!B(_6h(_ot,_nG))){return B(_6s(B(_jk(B(_el(E(_ox.a))),_lC)),B(_mJ(B(_jk(B(_jk(B(_el(E(_ox.b))),_lC)),_lC)),_ot))));}else{return E(_6c);}});},_oy=new T1(0,12345),_oz=function(_){var _oA=B(_ou(0)),_oB=B(_lX(B(_o9(_oA)).b,_cW,_lC,_cW)),_oC=_oB.b;if(!B(_6h(_oC,_kB))){var _oD=B(_6B(_oB.a,_oC));return new F(function(){return nMV(new T(function(){var _oE=B(_lE((B(_6p(B(_6s(B(_6s(B(_6s(B(_jk(_oD.a,_oy)),_oD.b)),_of)),_kB))))>>>0&2147483647)>>>0&4294967295,2147483562));return new T2(0,E(_oE.b)+1|0,B(_kD(E(_oE.a),2147483398))+1|0);}));});}else{return E(_6c);}},_oF=new T(function(){return B(_4n(_oz));}),_oG=function(_oH,_){var _oI=mMV(E(_oF),function(_oJ){var _oK=E(_oH),_oL=B(_lk(E(_oK.a),E(_oK.b),_oJ));return new T2(0,E(_oL.b),_oL.a);}),_oM=E(_oI);return _oI;},_oN=new T1(0,_7),_oO=new T(function(){return B(unCStr("!!: negative index"));}),_oP=new T(function(){return B(_2(_f3,_oO));}),_oQ=new T(function(){return B(err(_oP));}),_oR=new T(function(){return B(unCStr("!!: index too large"));}),_oS=new T(function(){return B(_2(_f3,_oR));}),_oT=new T(function(){return B(err(_oS));}),_oU=function(_oV,_oW){while(1){var _oX=E(_oV);if(!_oX._){return E(_oT);}else{var _oY=E(_oW);if(!_oY){return E(_oX.a);}else{_oV=_oX.b;_oW=_oY-1|0;continue;}}}},_oZ=function(_p0,_p1){if(_p1>=0){return new F(function(){return _oU(_p0,_p1);});}else{return E(_oQ);}},_p2=new T2(0,_2G,_C),_p3=new T0(2),_p4=function(_p5){return new T0(2);},_p6=function(_p7,_p8,_p9){return function(_){var _pa=E(_p7),_pb=rMV(_pa),_pc=E(_pb);if(!_pc._){var _pd=new T(function(){var _pe=new T(function(){return B(A1(_p9,_7));});return B(_2(_pc.b,new T2(1,new T2(0,_p8,function(_pf){return E(_pe);}),_6)));}),_=wMV(_pa,new T2(0,_pc.a,_pd));return _p3;}else{var _pg=E(_pc.a);if(!_pg._){var _=wMV(_pa,new T2(0,_p8,_6));return new T(function(){return B(A1(_p9,_7));});}else{var _=wMV(_pa,new T1(1,_pg.b));return new T1(1,new T2(1,new T(function(){return B(A1(_p9,_7));}),new T2(1,new T(function(){return B(A2(_pg.a,_p8,_p4));}),_6)));}}};},_ph=new T1(1,_6),_pi=function(_pj,_pk){return function(_){var _pl=E(_pj),_pm=rMV(_pl),_pn=E(_pm);if(!_pn._){var _po=_pn.a,_pp=E(_pn.b);if(!_pp._){var _=wMV(_pl,_ph);return new T(function(){return B(A1(_pk,_po));});}else{var _pq=E(_pp.a),_=wMV(_pl,new T2(0,_pq.a,_pp.b));return new T1(1,new T2(1,new T(function(){return B(A1(_pk,_po));}),new T2(1,new T(function(){return B(A1(_pq.b,_p4));}),_6)));}}else{var _pr=new T(function(){var _ps=function(_pt){var _pu=new T(function(){return B(A1(_pk,_pt));});return function(_pv){return E(_pu);};};return B(_2(_pn.a,new T2(1,_ps,_6)));}),_=wMV(_pl,new T1(1,_pr));return _p3;}};},_pw=function(_px){return E(E(_px).a);},_py=function(_pz){return E(E(_pz).a);},_pA=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_pB=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_pC=function(_pD){return E(E(_pD).b);},_pE=function(_pF){return E(E(_pF).b);},_pG=function(_pH,_pI,_pJ){var _pK=B(_pw(_pH)),_pL=new T(function(){return B(_pC(_pK));}),_pM=function(_pN){var _pO=function(_){var _pP=E(_pI);if(!_pP._){var _pQ=B(A1(_pN,_7)),_pR=__createJSFunc(0,function(_){var _pS=B(A1(_pQ,_));return _4r;}),_pT=__app2(E(_pB),_pP.a,_pR);return new T(function(){var _pU=Number(_pT),_pV=jsTrunc(_pU);return new T2(0,_pV,E(_pP));});}else{var _pW=B(A1(_pN,_7)),_pX=__createJSFunc(0,function(_){var _pY=B(A1(_pW,_));return _4r;}),_pZ=__app2(E(_pA),_pP.a,_pX);return new T(function(){var _q0=Number(_pZ),_q1=jsTrunc(_q0);return new T2(0,_q1,E(_pP));});}};return new F(function(){return A1(_pL,_pO);});},_q2=new T(function(){return B(A2(_pE,_pH,function(_q3){return E(_pJ);}));});return new F(function(){return A3(_ap,B(_py(_pK)),_q2,_pM);});},_q4=new T1(1,_6),_q5=function(_q6,_q7){return function(_){var _q8=nMV(_q4),_q9=_q8,_qa=function(_){var _qb=function(_){return new F(function(){return _e(new T(function(){return new T1(0,B(_p6(_q9,_7,_p4)));}),_6,_);});},_qc=B(A(_pG,[_p2,new T(function(){return new T1(0,E(_q6));}),_qb,_]));return new T(function(){return new T1(0,B(_pi(_q9,_q7)));});};return new T1(0,_qa);};},_qd=0,_qe=new T1(1,_6),_qf=function(_qg,_qh,_qi){return function(_){var _qj=nMV(_qe),_qk=_qj;return new T(function(){var _ql=function(_qm){var _qn=new T(function(){return B(A1(_qi,new T2(0,_7,E(_qm).b)));}),_qo=function(_qp){return E(_qn);};return new T1(0,B(_pi(_qk,function(_qq){return new T1(0,B(_q5(_qd,_qo)));})));},_qr=function(_qs,_qt){return new T1(0,B(_p6(_qk,_7,function(_qu){return new F(function(){return A1(_qt,new T2(0,_qu,_qs));});})));};return B(A3(_qg,_qr,_qh,_ql));});};},_qv=function(_qw){return E(E(_qw).a);},_qx=function(_qy,_qz,_qA,_qB,_){var _qC=E(_qy);switch(_qC._){case 0:return new F(function(){return A(_qz,[_qC.a,_qA,_qB,_]);});break;case 1:var _qD=B(A1(_qC.a,_));return new F(function(){return A(_qz,[_qD,_qA,_qB,_]);});break;case 2:var _qE=rMV(E(E(_qC.a).c)),_qF=E(_qE);if(!_qF._){var _qG=new T(function(){return B(A1(_qC.b,new T(function(){return B(_qv(_qF.a));})));});return new F(function(){return A(_qz,[_qG,_qA,_qB,_]);});}else{return _7;}break;default:var _qH=rMV(E(E(_qC.a).c)),_qI=E(_qH);if(!_qI._){var _qJ=B(A2(_qC.b,E(_qI.a).a,_));return new F(function(){return A(_qz,[_qJ,_qA,_qB,_]);});}else{return _7;}}},_qK=function(_qL,_qM,_){var _qN=E(_qL);switch(_qN._){case 0:return new F(function(){return A2(_qM,_qN.a,_);});break;case 1:var _qO=B(A1(_qN.a,_));return new F(function(){return A2(_qM,_qO,_);});break;case 2:var _qP=rMV(E(E(_qN.a).c)),_qQ=E(_qP);if(!_qQ._){var _qR=new T(function(){return B(A1(_qN.b,new T(function(){return B(_qv(_qQ.a));})));});return new F(function(){return A2(_qM,_qR,_);});}else{return _5i;}break;default:var _qS=rMV(E(E(_qN.a).c)),_qT=E(_qS);if(!_qT._){var _qU=B(A2(_qN.b,E(_qT.a).a,_));return new F(function(){return A2(_qM,_qU,_);});}else{return _5i;}}},_qV=function(_){return _7;},_qW=new T(function(){return eval("(function(x1,y1,x2,y2,x,y,ctx,_){ctx.bezierCurveTo(x1,y1,x2,y2,x,y);})");}),_qX=new T(function(){return eval("(function(x,y,ctx,_){ctx.moveTo(x,y);})");}),_qY=new T(function(){return 4*(Math.sqrt(2)-1)/3;}),_qZ=function(_r0,_r1,_r2){var _r3=function(_r4,_r5,_r6,_){var _r7=function(_r8,_r9,_ra,_){return new F(function(){return _qx(_r2,function(_rb,_rc,_rd,_){var _re=E(_r4),_rf=E(_r8),_rg=E(_rb),_rh=E(_rc),_ri=_rf-_rg,_rj=E(_rd),_rk=__app4(E(_qX),_re,_ri,_rh,_rj),_rl=E(_qY),_rm=E(_qW),_rn=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_rf,new T2(1,_re+_rg,new T2(1,_rf-_rg*_rl,new T2(1,_re+_rg,new T2(1,_ri,new T2(1,_re+_rg*_rl,_6))))))))),_ro=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_rf+_rg,new T2(1,_re,new T2(1,_rf+_rg,new T2(1,_re+_rg*_rl,new T2(1,_rf+_rg*_rl,new T2(1,_re+_rg,_6))))))))),_rp=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_rf,new T2(1,_re-_rg,new T2(1,_rf+_rg*_rl,new T2(1,_re-_rg,new T2(1,_rf+_rg,new T2(1,_re-_rg*_rl,_6))))))))),_rq=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_ri,new T2(1,_re,new T2(1,_ri,new T2(1,_re-_rg*_rl,new T2(1,_rf-_rg*_rl,new T2(1,_re-_rg,_6)))))))));return new F(function(){return _qV(_);});},_r9,_ra,_);});};return new F(function(){return _qx(_r1,_r7,_r5,_r6,_);});},_rr=function(_rs,_){var _rt=E(_rs),_ru=function(_rv,_){var _rw=function(_rx,_){var _ry=function(_rz,_){return new T(function(){var _rA=E(_rz),_rB=E(_rx)-E(_rt.b),_rC=E(_rv)-E(_rt.a);return _rC*_rC+_rB*_rB<=_rA*_rA;});};return new F(function(){return _qK(_r2,_ry,_);});};return new F(function(){return _qK(_r1,_rw,_);});};return new F(function(){return _qK(_r0,_ru,_);});};return new T3(0,_rr,function(_rD,_rE,_){return new F(function(){return _qx(_r0,_r3,_rD,_rE,_);});},_7);},_rF=function(_rG){return E(E(_rG).a);},_rH=function(_rI){return E(E(_rI).c);},_rJ=function(_rK){return E(E(_rK).b);},_rL=function(_rM,_rN,_rO){return new T1(0,B(_p6(_rM,_rN,_rO)));},_rP=function(_rQ,_rR){return new T1(0,B(_pi(_rQ,_rR)));},_rS=function(_rT,_rU,_rV){var _rW=new T(function(){return B(_rJ(_rT));}),_rX=B(_rF(_rT)),_rY=function(_rZ,_s0){var _s1=new T(function(){return B(A1(_rW,function(_s2){return new F(function(){return _rL(_rU,_s0,_s2);});}));});return new F(function(){return A3(_rH,_rX,_s1,new T(function(){return B(A2(_b1,_rX,_rZ));}));});},_s3=function(_s4){var _s5=E(_s4);return new F(function(){return _rY(_s5.a,_s5.b);});},_s6=function(_s7){return new F(function(){return A3(_ap,_rX,new T(function(){return B(A1(_rV,_s7));}),_s3);});},_s8=new T(function(){return B(A2(_rJ,_rT,function(_s2){return new F(function(){return _rP(_rU,_s2);});}));});return new F(function(){return A3(_ap,_rX,_s8,_s6);});},_s9=function(_sa,_sb,_sc){var _sd=new T(function(){return E(E(_sa).b);});return new F(function(){return A1(_sc,new T2(0,new T2(0,_7,new T2(0,new T(function(){return E(E(_sa).a);}),new T4(0,new T(function(){return E(E(_sd).a);}),new T(function(){return E(E(_sd).b);}),new T(function(){return E(E(_sd).c);}),_5i))),_sb));});},_se=0,_sf=function(_sg,_sh,_si,_sj){var _sk=function(_sl,_sm,_sn){return new F(function(){return A1(_sn,new T2(0,new T2(0,_7,new T(function(){var _so=E(_sl);return new T4(0,E(new T2(1,new T2(0,_sg,_sh),_so.a)),_so.b,E(_so.c),E(_so.d));})),_sm));});};return new F(function(){return A(_rS,[_4l,_si,_sk,_si,_sj]);});},_sp=function(_sq,_sr,_ss,_st,_su,_sv){var _sw=new T(function(){var _sx=new T(function(){return B(A1(_ss,_2E));}),_sy=function(_sz,_sA,_sB){var _sC=E(_sz),_sD=E(_sC.b),_sE=new T(function(){var _sF=new T(function(){return B(A1(_sx,new T(function(){return B(_a5(_sD.c,_sr));})));});return B(A3(_sq,_sF,_sD.a,_sD.b));});return new F(function(){return A1(_sB,new T2(0,new T2(0,_7,new T2(0,_sC.a,new T4(0,_sE,_su,_se,_sD.d))),_sA));});};return B(_rS(_4l,_st,_sy));}),_sG=new T(function(){return B(_rS(_4l,_st,_s9));}),_sH=new T(function(){var _sI=new T(function(){return B(A1(_sv,_5i));}),_sJ=new T(function(){return B(A1(_sv,_cm));}),_sK=new T(function(){return B(A1(_ss,_2E));}),_sL=function(_sM,_sN,_sO){var _sP=E(_sM),_sQ=E(_sP.b),_sR=_sQ.a,_sS=_sQ.b;if(!E(_sQ.d)){var _sT=E(_sr),_sU=E(_sQ.c)+1,_sV=function(_sW,_sX){var _sY=new T(function(){var _sZ=new T(function(){return B(A1(_sK,new T(function(){return _sW/_sT;})));});return B(A3(_sq,_sZ,_sR,_sS));}),_t0=new T4(0,_sR,_sS,_sX,_cm);if(_sW>=_sT){return new F(function(){return A2(_sJ,_sN,function(_t1){return new F(function(){return A1(_sO,new T2(0,new T2(0,_5i,new T2(0,_sY,_t0)),E(_t1).b));});});});}else{return new F(function(){return A1(_sO,new T2(0,new T2(0,_cm,new T2(0,_sY,_t0)),_sN));});}};if(_sT>_sU){return new F(function(){return _sV(_sU,_sU);});}else{return new F(function(){return _sV(_sT,_sT);});}}else{return new F(function(){return A2(_sI,_sN,function(_t2){return new F(function(){return A1(_sO,new T2(0,new T2(0,_5i,_sP),E(_t2).b));});});});}};return B(_rS(_4l,_st,_sL));}),_t3=function(_t4,_t5){var _t6=new T(function(){return B(A2(_sw,_t4,function(_t7){return new F(function(){return _sf(_sG,_sH,E(_t7).b,_t5);});}));}),_t8=function(_t9){var _ta=new T(function(){var _tb=E(_t9),_tc=E(_tb.a),_td=E(_tb.b),_te=E(_td.a),_tf=E(_td.b),_tg=E(_td.c),_th=E(_td.d);return E(_t6);});return new T1(0,B(_p6(_st,_t9,function(_ti){return E(_ta);})));};return new T1(0,B(_pi(_st,_t8)));};return E(_t3);},_tj=1,_tk=function(_tl,_tm){var _tn=new T(function(){var _to=function(_tp,_tq,_tr){return new F(function(){return A1(_tr,new T2(0,new T2(0,_7,new T2(0,_tm,new T4(0,_tm,_tm,_tj,new T(function(){return E(E(E(_tp).b).d);})))),_tq));});};return B(_rS(_4l,_tl,_to));}),_ts=function(_tt,_tu){var _tv=new T(function(){return B(A2(_tn,_tt,_tu));}),_tw=function(_tx){var _ty=new T(function(){var _tz=E(_tx),_tA=E(_tz.a),_tB=E(_tz.b),_tC=E(_tB.a),_tD=E(_tB.b),_tE=E(_tB.c),_tF=E(_tB.d);return E(_tv);});return new T1(0,B(_p6(_tl,_tx,function(_tG){return E(_ty);})));};return new T1(0,B(_pi(_tl,_tw)));};return E(_ts);},_tH=function(_tI,_tJ){var _tK=E(_tI);if(!_tK._){return __Z;}else{var _tL=_tK.a,_tM=E(_tJ);return (_tM==1)?new T2(1,new T(function(){var _tN=E(_tL),_tO=E(_tN.b);return new T2(0,_tO,_tN);}),_6):new T2(1,new T(function(){var _tP=E(_tL),_tQ=E(_tP.b);return new T2(0,_tQ,_tP);}),new T(function(){return B(_tH(_tK.b,_tM-1|0));}));}},_tR=function(_tS,_tT){while(1){var _tU=E(_tS);if(!_tU._){return E(_tT);}else{var _tV=_tT+1|0;_tS=_tU.b;_tT=_tV;continue;}}},_tW=function(_tX,_tY,_tZ,_u0,_u1,_){var _u2=function(_,_u3){var _u4=E(_tY);switch(_u4._){case 0:return new F(function(){return A(_tZ,[new T2(0,_u3,_u4.a),_u0,_u1,_]);});break;case 1:var _u5=B(A1(_u4.a,_));return new F(function(){return A(_tZ,[new T2(0,_u3,_u5),_u0,_u1,_]);});break;case 2:var _u6=rMV(E(E(_u4.a).c)),_u7=E(_u6);if(!_u7._){var _u8=new T(function(){return B(A1(_u4.b,new T(function(){return B(_qv(_u7.a));})));});return new F(function(){return A(_tZ,[new T2(0,_u3,_u8),_u0,_u1,_]);});}else{return _7;}break;default:var _u9=rMV(E(E(_u4.a).c)),_ua=E(_u9);if(!_ua._){var _ub=B(A2(_u4.b,E(_ua.a).a,_));return new F(function(){return A(_tZ,[new T2(0,_u3,_ub),_u0,_u1,_]);});}else{return _7;}}},_uc=E(_tX);switch(_uc._){case 0:return new F(function(){return _u2(_,_uc.a);});break;case 1:var _ud=B(A1(_uc.a,_));return new F(function(){return _u2(_,_ud);});break;case 2:var _ue=rMV(E(E(_uc.a).c)),_uf=E(_ue);if(!_uf._){var _ug=new T(function(){return B(A1(_uc.b,new T(function(){return E(E(_uf.a).a);})));});return new F(function(){return _u2(_,_ug);});}else{return _7;}break;default:var _uh=rMV(E(E(_uc.a).c)),_ui=E(_uh);if(!_ui._){var _uj=B(A2(_uc.b,E(_ui.a).a,_));return new F(function(){return _u2(_,_uj);});}else{return _7;}}},_uk=new T(function(){return eval("(function(x,y,ctx,_){ctx.lineTo(x,y);})");}),_ul=function(_um,_un,_uo,_up,_){var _uq=__app4(E(_uk),_um,_un,_uo,E(_up));return new F(function(){return _qV(_);});},_ur=function(_us,_ut){var _uu=function(_uv,_uw,_ux,_){var _uy=E(_ut);return new F(function(){return _tW(_uy.a,_uy.b,function(_uz,_uA,_uB,_){var _uC=E(_uv),_uD=E(_uA),_uE=E(_uB),_uF=__app4(E(_qX),E(_uC.a),E(_uC.b),_uD,_uE),_uG=E(_uz);return new F(function(){return _ul(E(_uG.a),E(_uG.b),_uD,_uE,_);});},_uw,_ux,_);});};return new T3(0,_5k,function(_uH,_uI,_){var _uJ=E(_us);return new F(function(){return _tW(_uJ.a,_uJ.b,_uu,_uH,_uI,_);});},_7);},_uK=function(_uL,_uM,_uN,_uO,_uP){var _uQ=E(_uP);if(!_uQ._){return __Z;}else{var _uR=E(_uQ.b),_uS=new T(function(){return B(_uK(new T(function(){return E(_uL)+E(_uO);}),new T(function(){var _uT=E(_uM),_uU=E(_uO);if(_uU>15){return _uT+1.5*_uU;}else{return _uT+22.5;}}),_cm,new T(function(){return E(_uO)/2;}),_uQ.c));});return new F(function(){return _2(B(_uK(new T(function(){return E(_uL)-E(_uO);}),new T(function(){var _uV=E(_uM),_uW=E(_uO);if(_uW>15){return _uV+1.5*_uW;}else{return _uV+22.5;}}),_5i,new T(function(){return E(_uO)/2;}),_uQ.a)),new T2(1,new T5(0,new T2(0,_uL,_uM),new T2(0,E(_uR.a).a,E(_uR.b).a),_uQ,_uO,_uN),_uS));});}},_uX=function(_uY,_uZ,_v0,_v1){while(1){var _v2=E(_v1);if(!_v2._){var _v3=E(_v2.b);if(_uY>_v3){_uZ=_v3;_v0=_v2.c;_v1=_v2.e;continue;}else{_v1=_v2.d;continue;}}else{return new T2(0,_uZ,_v0);}}},_v4=function(_v5,_v6){while(1){var _v7=E(_v6);if(!_v7._){var _v8=E(_v7.b);if(_v5>_v8){return new T1(1,B(_uX(_v5,_v8,_v7.c,_v7.e)));}else{_v6=_v7.d;continue;}}else{return __Z;}}},_v9=new T(function(){return eval("(function(ctx,_){ctx.restore();})");}),_va=new T(function(){return eval("(function(ctx,_){ctx.save();})");}),_vb=new T(function(){return eval("(function(x,y,ctx,_){ctx.scale(x,y);})");}),_vc=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");}),_vd=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");}),_ve=new T(function(){return eval("(function(x,y,ctx,_){ctx.translate(x,y);})");}),_vf="alphabetic",_vg="middle",_vh="hanging",_vi="right",_vj="center",_vk="left",_vl="(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",_vm=function(_vn,_vo,_vp,_vq,_vr,_vs,_vt){var _vu=function(_vv,_vw,_vx,_){var _vy=function(_vz,_vA,_vB,_){var _vC=function(_vD,_vE,_vF,_){var _vG=function(_vH,_vI,_vJ,_){var _vK=E(_vI),_vL=E(_vJ),_vM=__app2(E(_va),_vK,_vL),_vN=function(_vO){var _vP=function(_vQ){var _vR=eval(E(_vl)),_vS=__app4(E(_vR),E(_vn),_vO,_vQ,_vK),_vT=__app4(E(_ve),E(_vz),E(_vD),_vK,_vL),_vU=E(_vH)/10,_vV=__app4(E(_vb),_vU,_vU,_vK,_vL);if(!_vL){var _vW=__app5(E(_vc),toJSStr(E(_vv)),0,0,_vK,false),_vX=__app2(E(_v9),_vK,false);return new F(function(){return _qV(_);});}else{var _vY=__app5(E(_vd),toJSStr(E(_vv)),0,0,_vK,true),_vZ=__app2(E(_v9),_vK,true);return new F(function(){return _qV(_);});}};switch(E(_vq)){case 0:return new F(function(){return _vP(E(_vh));});break;case 1:return new F(function(){return _vP(E(_vg));});break;default:return new F(function(){return _vP(E(_vf));});}};switch(E(_vp)){case 0:return new F(function(){return _vN(E(_vk));});break;case 1:return new F(function(){return _vN(E(_vj));});break;default:return new F(function(){return _vN(E(_vi));});}};return new F(function(){return _qx(_vt,_vG,_vE,_vF,_);});};return new F(function(){return _qx(_vs,_vC,_vA,_vB,_);});};return new F(function(){return _qx(_vr,_vy,_vw,_vx,_);});};return new T3(0,_5k,function(_rD,_rE,_){return new F(function(){return _qx(_vo,_vu,_rD,_rE,_);});},_7);},_w0=function(_w1,_w2,_w3,_w4,_w5,_w6){return (_w1!=_w4)?true:(E(_w2)!=E(_w5))?true:(E(_w3)!=E(_w6))?true:false;},_w7=function(_w8,_w9){var _wa=E(_w8),_wb=E(_w9);return new F(function(){return _w0(E(_wa.a),_wa.b,_wa.c,E(_wb.a),_wb.b,_wb.c);});},_wc=function(_wd,_we){return E(_wd)==E(_we);},_wf=function(_wg,_wh,_wi,_wj,_wk,_wl){if(_wg!=_wj){return false;}else{if(E(_wh)!=E(_wk)){return false;}else{return new F(function(){return _wc(_wi,_wl);});}}},_wm=function(_wn,_wo){var _wp=E(_wn),_wq=E(_wo);return new F(function(){return _wf(E(_wp.a),_wp.b,_wp.c,E(_wq.a),_wq.b,_wq.c);});},_wr=new T2(0,_wm,_w7),_ws=__Z,_wt=function(_wu){return E(E(_wu).b);},_wv=new T0(1),_ww=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_wx=function(_wy){return new F(function(){return err(_ww);});},_wz=new T(function(){return B(_wx(_));}),_wA=function(_wB,_wC,_wD,_wE){var _wF=E(_wE);if(!_wF._){var _wG=_wF.a,_wH=E(_wD);if(!_wH._){var _wI=_wH.a,_wJ=_wH.b,_wK=_wH.c;if(_wI<=(imul(3,_wG)|0)){return new T5(0,(1+_wI|0)+_wG|0,E(_wB),_wC,E(_wH),E(_wF));}else{var _wL=E(_wH.d);if(!_wL._){var _wM=_wL.a,_wN=E(_wH.e);if(!_wN._){var _wO=_wN.a,_wP=_wN.b,_wQ=_wN.c,_wR=_wN.d;if(_wO>=(imul(2,_wM)|0)){var _wS=function(_wT){var _wU=E(_wN.e);return (_wU._==0)?new T5(0,(1+_wI|0)+_wG|0,E(_wP),_wQ,E(new T5(0,(1+_wM|0)+_wT|0,E(_wJ),_wK,E(_wL),E(_wR))),E(new T5(0,(1+_wG|0)+_wU.a|0,E(_wB),_wC,E(_wU),E(_wF)))):new T5(0,(1+_wI|0)+_wG|0,E(_wP),_wQ,E(new T5(0,(1+_wM|0)+_wT|0,E(_wJ),_wK,E(_wL),E(_wR))),E(new T5(0,1+_wG|0,E(_wB),_wC,E(_wv),E(_wF))));},_wV=E(_wR);if(!_wV._){return new F(function(){return _wS(_wV.a);});}else{return new F(function(){return _wS(0);});}}else{return new T5(0,(1+_wI|0)+_wG|0,E(_wJ),_wK,E(_wL),E(new T5(0,(1+_wG|0)+_wO|0,E(_wB),_wC,E(_wN),E(_wF))));}}else{return E(_wz);}}else{return E(_wz);}}}else{return new T5(0,1+_wG|0,E(_wB),_wC,E(_wv),E(_wF));}}else{var _wW=E(_wD);if(!_wW._){var _wX=_wW.a,_wY=_wW.b,_wZ=_wW.c,_x0=_wW.e,_x1=E(_wW.d);if(!_x1._){var _x2=_x1.a,_x3=E(_x0);if(!_x3._){var _x4=_x3.a,_x5=_x3.b,_x6=_x3.c,_x7=_x3.d;if(_x4>=(imul(2,_x2)|0)){var _x8=function(_x9){var _xa=E(_x3.e);return (_xa._==0)?new T5(0,1+_wX|0,E(_x5),_x6,E(new T5(0,(1+_x2|0)+_x9|0,E(_wY),_wZ,E(_x1),E(_x7))),E(new T5(0,1+_xa.a|0,E(_wB),_wC,E(_xa),E(_wv)))):new T5(0,1+_wX|0,E(_x5),_x6,E(new T5(0,(1+_x2|0)+_x9|0,E(_wY),_wZ,E(_x1),E(_x7))),E(new T5(0,1,E(_wB),_wC,E(_wv),E(_wv))));},_xb=E(_x7);if(!_xb._){return new F(function(){return _x8(_xb.a);});}else{return new F(function(){return _x8(0);});}}else{return new T5(0,1+_wX|0,E(_wY),_wZ,E(_x1),E(new T5(0,1+_x4|0,E(_wB),_wC,E(_x3),E(_wv))));}}else{return new T5(0,3,E(_wY),_wZ,E(_x1),E(new T5(0,1,E(_wB),_wC,E(_wv),E(_wv))));}}else{var _xc=E(_x0);return (_xc._==0)?new T5(0,3,E(_xc.b),_xc.c,E(new T5(0,1,E(_wY),_wZ,E(_wv),E(_wv))),E(new T5(0,1,E(_wB),_wC,E(_wv),E(_wv)))):new T5(0,2,E(_wB),_wC,E(_wW),E(_wv));}}else{return new T5(0,1,E(_wB),_wC,E(_wv),E(_wv));}}},_xd=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_xe=function(_xf){return new F(function(){return err(_xd);});},_xg=new T(function(){return B(_xe(_));}),_xh=function(_xi,_xj,_xk,_xl){var _xm=E(_xk);if(!_xm._){var _xn=_xm.a,_xo=E(_xl);if(!_xo._){var _xp=_xo.a,_xq=_xo.b,_xr=_xo.c;if(_xp<=(imul(3,_xn)|0)){return new T5(0,(1+_xn|0)+_xp|0,E(_xi),_xj,E(_xm),E(_xo));}else{var _xs=E(_xo.d);if(!_xs._){var _xt=_xs.a,_xu=_xs.b,_xv=_xs.c,_xw=_xs.d,_xx=E(_xo.e);if(!_xx._){var _xy=_xx.a;if(_xt>=(imul(2,_xy)|0)){var _xz=function(_xA){var _xB=E(_xi),_xC=E(_xs.e);return (_xC._==0)?new T5(0,(1+_xn|0)+_xp|0,E(_xu),_xv,E(new T5(0,(1+_xn|0)+_xA|0,E(_xB),_xj,E(_xm),E(_xw))),E(new T5(0,(1+_xy|0)+_xC.a|0,E(_xq),_xr,E(_xC),E(_xx)))):new T5(0,(1+_xn|0)+_xp|0,E(_xu),_xv,E(new T5(0,(1+_xn|0)+_xA|0,E(_xB),_xj,E(_xm),E(_xw))),E(new T5(0,1+_xy|0,E(_xq),_xr,E(_wv),E(_xx))));},_xD=E(_xw);if(!_xD._){return new F(function(){return _xz(_xD.a);});}else{return new F(function(){return _xz(0);});}}else{return new T5(0,(1+_xn|0)+_xp|0,E(_xq),_xr,E(new T5(0,(1+_xn|0)+_xt|0,E(_xi),_xj,E(_xm),E(_xs))),E(_xx));}}else{return E(_xg);}}else{return E(_xg);}}}else{return new T5(0,1+_xn|0,E(_xi),_xj,E(_xm),E(_wv));}}else{var _xE=E(_xl);if(!_xE._){var _xF=_xE.a,_xG=_xE.b,_xH=_xE.c,_xI=_xE.e,_xJ=E(_xE.d);if(!_xJ._){var _xK=_xJ.a,_xL=_xJ.b,_xM=_xJ.c,_xN=_xJ.d,_xO=E(_xI);if(!_xO._){var _xP=_xO.a;if(_xK>=(imul(2,_xP)|0)){var _xQ=function(_xR){var _xS=E(_xi),_xT=E(_xJ.e);return (_xT._==0)?new T5(0,1+_xF|0,E(_xL),_xM,E(new T5(0,1+_xR|0,E(_xS),_xj,E(_wv),E(_xN))),E(new T5(0,(1+_xP|0)+_xT.a|0,E(_xG),_xH,E(_xT),E(_xO)))):new T5(0,1+_xF|0,E(_xL),_xM,E(new T5(0,1+_xR|0,E(_xS),_xj,E(_wv),E(_xN))),E(new T5(0,1+_xP|0,E(_xG),_xH,E(_wv),E(_xO))));},_xU=E(_xN);if(!_xU._){return new F(function(){return _xQ(_xU.a);});}else{return new F(function(){return _xQ(0);});}}else{return new T5(0,1+_xF|0,E(_xG),_xH,E(new T5(0,1+_xK|0,E(_xi),_xj,E(_wv),E(_xJ))),E(_xO));}}else{return new T5(0,3,E(_xL),_xM,E(new T5(0,1,E(_xi),_xj,E(_wv),E(_wv))),E(new T5(0,1,E(_xG),_xH,E(_wv),E(_wv))));}}else{var _xV=E(_xI);return (_xV._==0)?new T5(0,3,E(_xG),_xH,E(new T5(0,1,E(_xi),_xj,E(_wv),E(_wv))),E(_xV)):new T5(0,2,E(_xi),_xj,E(_wv),E(_xE));}}else{return new T5(0,1,E(_xi),_xj,E(_wv),E(_wv));}}},_xW=function(_xX,_xY){return new T5(0,1,E(_xX),_xY,E(_wv),E(_wv));},_xZ=function(_y0,_y1,_y2){var _y3=E(_y2);if(!_y3._){return new F(function(){return _xh(_y3.b,_y3.c,_y3.d,B(_xZ(_y0,_y1,_y3.e)));});}else{return new F(function(){return _xW(_y0,_y1);});}},_y4=function(_y5,_y6,_y7){var _y8=E(_y7);if(!_y8._){return new F(function(){return _wA(_y8.b,_y8.c,B(_y4(_y5,_y6,_y8.d)),_y8.e);});}else{return new F(function(){return _xW(_y5,_y6);});}},_y9=function(_ya,_yb,_yc,_yd,_ye,_yf,_yg){return new F(function(){return _wA(_yd,_ye,B(_y4(_ya,_yb,_yf)),_yg);});},_yh=function(_yi,_yj,_yk,_yl,_ym,_yn,_yo,_yp){var _yq=E(_yk);if(!_yq._){var _yr=_yq.a,_ys=_yq.b,_yt=_yq.c,_yu=_yq.d,_yv=_yq.e;if((imul(3,_yr)|0)>=_yl){if((imul(3,_yl)|0)>=_yr){return new T5(0,(_yr+_yl|0)+1|0,E(_yi),_yj,E(_yq),E(new T5(0,_yl,E(_ym),_yn,E(_yo),E(_yp))));}else{return new F(function(){return _xh(_ys,_yt,_yu,B(_yh(_yi,_yj,_yv,_yl,_ym,_yn,_yo,_yp)));});}}else{return new F(function(){return _wA(_ym,_yn,B(_yw(_yi,_yj,_yr,_ys,_yt,_yu,_yv,_yo)),_yp);});}}else{return new F(function(){return _y9(_yi,_yj,_yl,_ym,_yn,_yo,_yp);});}},_yw=function(_yx,_yy,_yz,_yA,_yB,_yC,_yD,_yE){var _yF=E(_yE);if(!_yF._){var _yG=_yF.a,_yH=_yF.b,_yI=_yF.c,_yJ=_yF.d,_yK=_yF.e;if((imul(3,_yz)|0)>=_yG){if((imul(3,_yG)|0)>=_yz){return new T5(0,(_yz+_yG|0)+1|0,E(_yx),_yy,E(new T5(0,_yz,E(_yA),_yB,E(_yC),E(_yD))),E(_yF));}else{return new F(function(){return _xh(_yA,_yB,_yC,B(_yh(_yx,_yy,_yD,_yG,_yH,_yI,_yJ,_yK)));});}}else{return new F(function(){return _wA(_yH,_yI,B(_yw(_yx,_yy,_yz,_yA,_yB,_yC,_yD,_yJ)),_yK);});}}else{return new F(function(){return _xZ(_yx,_yy,new T5(0,_yz,E(_yA),_yB,E(_yC),E(_yD)));});}},_yL=function(_yM,_yN,_yO,_yP){var _yQ=E(_yO);if(!_yQ._){var _yR=_yQ.a,_yS=_yQ.b,_yT=_yQ.c,_yU=_yQ.d,_yV=_yQ.e,_yW=E(_yP);if(!_yW._){var _yX=_yW.a,_yY=_yW.b,_yZ=_yW.c,_z0=_yW.d,_z1=_yW.e;if((imul(3,_yR)|0)>=_yX){if((imul(3,_yX)|0)>=_yR){return new T5(0,(_yR+_yX|0)+1|0,E(_yM),_yN,E(_yQ),E(_yW));}else{return new F(function(){return _xh(_yS,_yT,_yU,B(_yh(_yM,_yN,_yV,_yX,_yY,_yZ,_z0,_z1)));});}}else{return new F(function(){return _wA(_yY,_yZ,B(_yw(_yM,_yN,_yR,_yS,_yT,_yU,_yV,_z0)),_z1);});}}else{return new F(function(){return _xZ(_yM,_yN,_yQ);});}}else{return new F(function(){return _y4(_yM,_yN,_yP);});}},_z2=function(_z3,_z4,_z5){var _z6=E(_z4);if(!_z6._){return E(_z5);}else{var _z7=function(_z8,_z9){while(1){var _za=E(_z9);if(!_za._){var _zb=_za.b,_zc=_za.e;switch(B(A3(_wt,_z3,_z8,_zb))){case 0:return new F(function(){return _yL(_zb,_za.c,B(_z7(_z8,_za.d)),_zc);});break;case 1:return E(_zc);default:_z9=_zc;continue;}}else{return new T0(1);}}};return new F(function(){return _z7(_z6.a,_z5);});}},_zd=function(_ze,_zf,_zg){var _zh=E(_zf);if(!_zh._){return E(_zg);}else{var _zi=function(_zj,_zk){while(1){var _zl=E(_zk);if(!_zl._){var _zm=_zl.b,_zn=_zl.d;switch(B(A3(_wt,_ze,_zm,_zj))){case 0:return new F(function(){return _yL(_zm,_zl.c,_zn,B(_zi(_zj,_zl.e)));});break;case 1:return E(_zn);default:_zk=_zn;continue;}}else{return new T0(1);}}};return new F(function(){return _zi(_zh.a,_zg);});}},_zo=function(_zp,_zq,_zr,_zs){var _zt=E(_zq),_zu=E(_zs);if(!_zu._){var _zv=_zu.b,_zw=_zu.c,_zx=_zu.d,_zy=_zu.e;switch(B(A3(_wt,_zp,_zt,_zv))){case 0:return new F(function(){return _wA(_zv,_zw,B(_zo(_zp,_zt,_zr,_zx)),_zy);});break;case 1:return E(_zu);default:return new F(function(){return _xh(_zv,_zw,_zx,B(_zo(_zp,_zt,_zr,_zy)));});}}else{return new T5(0,1,E(_zt),_zr,E(_wv),E(_wv));}},_zz=function(_zA,_zB,_zC,_zD){return new F(function(){return _zo(_zA,_zB,_zC,_zD);});},_zE=function(_zF){return E(E(_zF).d);},_zG=function(_zH){return E(E(_zH).f);},_zI=function(_zJ,_zK,_zL,_zM){var _zN=E(_zK);if(!_zN._){var _zO=E(_zL);if(!_zO._){return E(_zM);}else{var _zP=function(_zQ,_zR){while(1){var _zS=E(_zR);if(!_zS._){if(!B(A3(_zG,_zJ,_zS.b,_zQ))){return E(_zS);}else{_zR=_zS.d;continue;}}else{return new T0(1);}}};return new F(function(){return _zP(_zO.a,_zM);});}}else{var _zT=_zN.a,_zU=E(_zL);if(!_zU._){var _zV=function(_zW,_zX){while(1){var _zY=E(_zX);if(!_zY._){if(!B(A3(_zE,_zJ,_zY.b,_zW))){return E(_zY);}else{_zX=_zY.e;continue;}}else{return new T0(1);}}};return new F(function(){return _zV(_zT,_zM);});}else{var _zZ=function(_A0,_A1,_A2){while(1){var _A3=E(_A2);if(!_A3._){var _A4=_A3.b;if(!B(A3(_zE,_zJ,_A4,_A0))){if(!B(A3(_zG,_zJ,_A4,_A1))){return E(_A3);}else{_A2=_A3.d;continue;}}else{_A2=_A3.e;continue;}}else{return new T0(1);}}};return new F(function(){return _zZ(_zT,_zU.a,_zM);});}}},_A5=function(_A6,_A7,_A8,_A9,_Aa){var _Ab=E(_Aa);if(!_Ab._){var _Ac=_Ab.b,_Ad=_Ab.c,_Ae=_Ab.d,_Af=_Ab.e,_Ag=E(_A9);if(!_Ag._){var _Ah=_Ag.b,_Ai=function(_Aj){var _Ak=new T1(1,E(_Ah));return new F(function(){return _yL(_Ah,_Ag.c,B(_A5(_A6,_A7,_Ak,_Ag.d,B(_zI(_A6,_A7,_Ak,_Ab)))),B(_A5(_A6,_Ak,_A8,_Ag.e,B(_zI(_A6,_Ak,_A8,_Ab)))));});};if(!E(_Ae)._){return new F(function(){return _Ai(_);});}else{if(!E(_Af)._){return new F(function(){return _Ai(_);});}else{return new F(function(){return _zz(_A6,_Ac,_Ad,_Ag);});}}}else{return new F(function(){return _yL(_Ac,_Ad,B(_z2(_A6,_A7,_Ae)),B(_zd(_A6,_A8,_Af)));});}}else{return E(_A9);}},_Al=function(_Am,_An,_Ao,_Ap,_Aq,_Ar,_As,_At,_Au,_Av,_Aw,_Ax,_Ay){var _Az=function(_AA){var _AB=new T1(1,E(_Aq));return new F(function(){return _yL(_Aq,_Ar,B(_A5(_Am,_An,_AB,_As,B(_zI(_Am,_An,_AB,new T5(0,_Au,E(_Av),_Aw,E(_Ax),E(_Ay)))))),B(_A5(_Am,_AB,_Ao,_At,B(_zI(_Am,_AB,_Ao,new T5(0,_Au,E(_Av),_Aw,E(_Ax),E(_Ay)))))));});};if(!E(_Ax)._){return new F(function(){return _Az(_);});}else{if(!E(_Ay)._){return new F(function(){return _Az(_);});}else{return new F(function(){return _zz(_Am,_Av,_Aw,new T5(0,_Ap,E(_Aq),_Ar,E(_As),E(_At)));});}}},_AC=function(_AD,_AE){var _AF=E(_AD);if(!_AF._){var _AG=E(_AE);if(!_AG._){return new F(function(){return _Al(_bP,_ws,_ws,_AF.a,_AF.b,_AF.c,_AF.d,_AF.e,_AG.a,_AG.b,_AG.c,_AG.d,_AG.e);});}else{return E(_AF);}}else{return E(_AE);}},_AH=function(_AI,_AJ,_AK,_AL){return (_AI!=_AK)?true:(E(_AJ)!=E(_AL))?true:false;},_AM=function(_AN,_AO){var _AP=E(_AN),_AQ=E(_AO);return new F(function(){return _AH(E(_AP.a),_AP.b,E(_AQ.a),_AQ.b);});},_AR=function(_AS,_AT,_AU,_AV){if(_AS!=_AU){return false;}else{return new F(function(){return _bk(_AT,_AV);});}},_AW=function(_AX,_AY){var _AZ=E(_AX),_B0=E(_AY);return new F(function(){return _AR(E(_AZ.a),_AZ.b,E(_B0.a),_B0.b);});},_B1=new T2(0,_AW,_AM),_B2=function(_B3,_B4,_B5,_B6,_B7,_B8,_B9,_Ba,_Bb,_Bc,_Bd,_Be,_Bf,_Bg,_Bh,_Bi,_Bj,_Bk,_Bl,_Bm,_Bn,_Bo,_Bp,_Bq){if(_B3!=_Bf){return false;}else{if(_B4!=_Bg){return false;}else{if(_B5!=_Bh){return false;}else{if(_B6!=_Bi){return false;}else{if(_B7!=_Bj){return false;}else{if(_B8!=_Bk){return false;}else{if(_B9!=_Bl){return false;}else{if(_Ba!=_Bm){return false;}else{if(_Bb!=_Bn){return false;}else{if(_Bc!=_Bo){return false;}else{if(E(_Bd)!=E(_Bp)){return false;}else{return new F(function(){return _bk(_Be,_Bq);});}}}}}}}}}}}},_Br=function(_Bs,_Bt){var _Bu=E(_Bs),_Bv=E(_Bu.a),_Bw=E(_Bu.b),_Bx=E(_Bu.c),_By=E(_Bu.e),_Bz=E(_Bt),_BA=E(_Bz.a),_BB=E(_Bz.b),_BC=E(_Bz.c),_BD=E(_Bz.e);return new F(function(){return _B2(_Bv.a,_Bv.b,_Bv.c,_Bw.a,_Bw.b,_Bw.c,_Bx.a,_Bx.b,_Bx.c,_Bu.d,_By.a,_By.b,_BA.a,_BA.b,_BA.c,_BB.a,_BB.b,_BB.c,_BC.a,_BC.b,_BC.c,_Bz.d,_BD.a,_BD.b);});},_BE=function(_BF,_BG,_BH,_BI,_BJ,_BK){if(_BF!=_BI){return false;}else{var _BL=E(_BG),_BM=E(_BJ);if(E(_BL.a)!=E(_BM.a)){return false;}else{if(E(_BL.b)!=E(_BM.b)){return false;}else{if(E(_BL.c)!=E(_BM.c)){return false;}else{return new F(function(){return _Br(_BH,_BK);});}}}}},_BN=function(_BO,_BP){var _BQ=E(_BO),_BR=E(_BP);return new F(function(){return _BE(E(_BQ.a),_BQ.b,_BQ.c,E(_BR.a),_BR.b,_BR.c);});},_BS=function(_BT,_BU,_BV,_BW,_BX,_BY){if(_BT!=_BW){return true;}else{var _BZ=E(_BU),_C0=E(_BX);if(E(_BZ.a)!=E(_C0.a)){return true;}else{if(E(_BZ.b)!=E(_C0.b)){return true;}else{if(E(_BZ.c)!=E(_C0.c)){return true;}else{var _C1=E(_BV),_C2=E(_C1.a),_C3=E(_C1.b),_C4=E(_C1.c),_C5=E(_C1.e),_C6=E(_BY),_C7=E(_C6.a),_C8=E(_C6.b),_C9=E(_C6.c),_Ca=E(_C6.e);return (_C2.a!=_C7.a)?true:(_C2.b!=_C7.b)?true:(_C2.c!=_C7.c)?true:(_C3.a!=_C8.a)?true:(_C3.b!=_C8.b)?true:(_C3.c!=_C8.c)?true:(_C4.a!=_C9.a)?true:(_C4.b!=_C9.b)?true:(_C4.c!=_C9.c)?true:(_C1.d!=_C6.d)?true:(E(_C5.a)!=E(_Ca.a))?true:(E(_C5.b)!=E(_Ca.b))?true:false;}}}}},_Cb=function(_Cc,_Cd){var _Ce=E(_Cc),_Cf=E(_Cd);return new F(function(){return _BS(E(_Ce.a),_Ce.b,_Ce.c,E(_Cf.a),_Cf.b,_Cf.c);});},_Cg=new T2(0,_BN,_Cb),_Ch=function(_Ci,_Cj,_Ck,_Cl,_Cm,_Cn,_Co,_Cp,_Cq,_Cr,_Cs,_Ct,_Cu,_Cv,_Cw,_Cx,_Cy,_Cz,_CA,_CB,_CC,_CD,_CE,_CF){if(_Ci>=_Cu){if(_Ci!=_Cu){return 2;}else{if(_Cj>=_Cv){if(_Cj!=_Cv){return 2;}else{if(_Ck>=_Cw){if(_Ck!=_Cw){return 2;}else{if(_Cl>=_Cx){if(_Cl!=_Cx){return 2;}else{if(_Cm>=_Cy){if(_Cm!=_Cy){return 2;}else{if(_Cn>=_Cz){if(_Cn!=_Cz){return 2;}else{if(_Co>=_CA){if(_Co!=_CA){return 2;}else{if(_Cp>=_CB){if(_Cp!=_CB){return 2;}else{if(_Cq>=_CC){if(_Cq!=_CC){return 2;}else{if(_Cr>=_CD){if(_Cr!=_CD){return 2;}else{var _CG=E(_Cs),_CH=E(_CE);if(_CG>=_CH){if(_CG!=_CH){return 2;}else{return new F(function(){return _bA(_Ct,_CF);});}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}},_CI=function(_CJ,_CK){var _CL=E(_CJ),_CM=E(_CL.a),_CN=E(_CL.b),_CO=E(_CL.c),_CP=E(_CL.e),_CQ=E(_CK),_CR=E(_CQ.a),_CS=E(_CQ.b),_CT=E(_CQ.c),_CU=E(_CQ.e);return new F(function(){return _Ch(_CM.a,_CM.b,_CM.c,_CN.a,_CN.b,_CN.c,_CO.a,_CO.b,_CO.c,_CL.d,_CP.a,_CP.b,_CR.a,_CR.b,_CR.c,_CS.a,_CS.b,_CS.c,_CT.a,_CT.b,_CT.c,_CQ.d,_CU.a,_CU.b);});},_CV=function(_CW,_CX,_CY,_CZ,_D0,_D1){if(_CW>=_CZ){if(_CW!=_CZ){return 2;}else{var _D2=E(_CX),_D3=E(_D0),_D4=E(_D2.a),_D5=E(_D3.a);if(_D4>=_D5){if(_D4!=_D5){return 2;}else{var _D6=E(_D2.b),_D7=E(_D3.b);if(_D6>=_D7){if(_D6!=_D7){return 2;}else{var _D8=E(_D2.c),_D9=E(_D3.c);if(_D8>=_D9){if(_D8!=_D9){return 2;}else{return new F(function(){return _CI(_CY,_D1);});}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}},_Da=function(_Db,_Dc){var _Dd=E(_Db),_De=E(_Dc);return new F(function(){return _CV(E(_Dd.a),_Dd.b,_Dd.c,E(_De.a),_De.b,_De.c);});},_Df=function(_Dg,_Dh,_Di,_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy,_Dz,_DA,_DB,_DC,_DD){if(_Dg>=_Ds){if(_Dg!=_Ds){return false;}else{if(_Dh>=_Dt){if(_Dh!=_Dt){return false;}else{if(_Di>=_Du){if(_Di!=_Du){return false;}else{if(_Dj>=_Dv){if(_Dj!=_Dv){return false;}else{if(_Dk>=_Dw){if(_Dk!=_Dw){return false;}else{if(_Dl>=_Dx){if(_Dl!=_Dx){return false;}else{if(_Dm>=_Dy){if(_Dm!=_Dy){return false;}else{if(_Dn>=_Dz){if(_Dn!=_Dz){return false;}else{if(_Do>=_DA){if(_Do!=_DA){return false;}else{if(_Dp>=_DB){if(_Dp!=_DB){return false;}else{var _DE=E(_Dq),_DF=E(_DC);if(_DE>=_DF){if(_DE!=_DF){return false;}else{return new F(function(){return _bo(_Dr,_DD);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_DG=function(_DH,_DI){var _DJ=E(_DH),_DK=E(_DJ.a),_DL=E(_DJ.b),_DM=E(_DJ.c),_DN=E(_DJ.e),_DO=E(_DI),_DP=E(_DO.a),_DQ=E(_DO.b),_DR=E(_DO.c),_DS=E(_DO.e);return new F(function(){return _Df(_DK.a,_DK.b,_DK.c,_DL.a,_DL.b,_DL.c,_DM.a,_DM.b,_DM.c,_DJ.d,_DN.a,_DN.b,_DP.a,_DP.b,_DP.c,_DQ.a,_DQ.b,_DQ.c,_DR.a,_DR.b,_DR.c,_DO.d,_DS.a,_DS.b);});},_DT=function(_DU,_DV,_DW,_DX,_DY,_DZ){if(_DU>=_DX){if(_DU!=_DX){return false;}else{var _E0=E(_DV),_E1=E(_DY),_E2=E(_E0.a),_E3=E(_E1.a);if(_E2>=_E3){if(_E2!=_E3){return false;}else{var _E4=E(_E0.b),_E5=E(_E1.b);if(_E4>=_E5){if(_E4!=_E5){return false;}else{var _E6=E(_E0.c),_E7=E(_E1.c);if(_E6>=_E7){if(_E6!=_E7){return false;}else{return new F(function(){return _DG(_DW,_DZ);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_E8=function(_E9,_Ea){var _Eb=E(_E9),_Ec=E(_Ea);return new F(function(){return _DT(E(_Eb.a),_Eb.b,_Eb.c,E(_Ec.a),_Ec.b,_Ec.c);});},_Ed=function(_Ee,_Ef,_Eg,_Eh,_Ei,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew,_Ex,_Ey,_Ez,_EA,_EB){if(_Ee>=_Eq){if(_Ee!=_Eq){return false;}else{if(_Ef>=_Er){if(_Ef!=_Er){return false;}else{if(_Eg>=_Es){if(_Eg!=_Es){return false;}else{if(_Eh>=_Et){if(_Eh!=_Et){return false;}else{if(_Ei>=_Eu){if(_Ei!=_Eu){return false;}else{if(_Ej>=_Ev){if(_Ej!=_Ev){return false;}else{if(_Ek>=_Ew){if(_Ek!=_Ew){return false;}else{if(_El>=_Ex){if(_El!=_Ex){return false;}else{if(_Em>=_Ey){if(_Em!=_Ey){return false;}else{if(_En>=_Ez){if(_En!=_Ez){return false;}else{var _EC=E(_Eo),_ED=E(_EA);if(_EC>=_ED){if(_EC!=_ED){return false;}else{return new F(function(){return _br(_Ep,_EB);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_EE=function(_EF,_EG){var _EH=E(_EF),_EI=E(_EH.a),_EJ=E(_EH.b),_EK=E(_EH.c),_EL=E(_EH.e),_EM=E(_EG),_EN=E(_EM.a),_EO=E(_EM.b),_EP=E(_EM.c),_EQ=E(_EM.e);return new F(function(){return _Ed(_EI.a,_EI.b,_EI.c,_EJ.a,_EJ.b,_EJ.c,_EK.a,_EK.b,_EK.c,_EH.d,_EL.a,_EL.b,_EN.a,_EN.b,_EN.c,_EO.a,_EO.b,_EO.c,_EP.a,_EP.b,_EP.c,_EM.d,_EQ.a,_EQ.b);});},_ER=function(_ES,_ET,_EU,_EV,_EW,_EX){if(_ES>=_EV){if(_ES!=_EV){return false;}else{var _EY=E(_ET),_EZ=E(_EW),_F0=E(_EY.a),_F1=E(_EZ.a);if(_F0>=_F1){if(_F0!=_F1){return false;}else{var _F2=E(_EY.b),_F3=E(_EZ.b);if(_F2>=_F3){if(_F2!=_F3){return false;}else{var _F4=E(_EY.c),_F5=E(_EZ.c);if(_F4>=_F5){if(_F4!=_F5){return false;}else{return new F(function(){return _EE(_EU,_EX);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_F6=function(_F7,_F8){var _F9=E(_F7),_Fa=E(_F8);return new F(function(){return _ER(E(_F9.a),_F9.b,_F9.c,E(_Fa.a),_Fa.b,_Fa.c);});},_Fb=function(_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo,_Fp,_Fq,_Fr,_Fs,_Ft,_Fu,_Fv,_Fw,_Fx,_Fy,_Fz){if(_Fc>=_Fo){if(_Fc!=_Fo){return true;}else{if(_Fd>=_Fp){if(_Fd!=_Fp){return true;}else{if(_Fe>=_Fq){if(_Fe!=_Fq){return true;}else{if(_Ff>=_Fr){if(_Ff!=_Fr){return true;}else{if(_Fg>=_Fs){if(_Fg!=_Fs){return true;}else{if(_Fh>=_Ft){if(_Fh!=_Ft){return true;}else{if(_Fi>=_Fu){if(_Fi!=_Fu){return true;}else{if(_Fj>=_Fv){if(_Fj!=_Fv){return true;}else{if(_Fk>=_Fw){if(_Fk!=_Fw){return true;}else{if(_Fl>=_Fx){if(_Fl!=_Fx){return true;}else{var _FA=E(_Fm),_FB=E(_Fy);if(_FA>=_FB){if(_FA!=_FB){return true;}else{return new F(function(){return _bu(_Fn,_Fz);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_FC=function(_FD,_FE){var _FF=E(_FD),_FG=E(_FF.a),_FH=E(_FF.b),_FI=E(_FF.c),_FJ=E(_FF.e),_FK=E(_FE),_FL=E(_FK.a),_FM=E(_FK.b),_FN=E(_FK.c),_FO=E(_FK.e);return new F(function(){return _Fb(_FG.a,_FG.b,_FG.c,_FH.a,_FH.b,_FH.c,_FI.a,_FI.b,_FI.c,_FF.d,_FJ.a,_FJ.b,_FL.a,_FL.b,_FL.c,_FM.a,_FM.b,_FM.c,_FN.a,_FN.b,_FN.c,_FK.d,_FO.a,_FO.b);});},_FP=function(_FQ,_FR,_FS,_FT,_FU,_FV){if(_FQ>=_FT){if(_FQ!=_FT){return true;}else{var _FW=E(_FR),_FX=E(_FU),_FY=E(_FW.a),_FZ=E(_FX.a);if(_FY>=_FZ){if(_FY!=_FZ){return true;}else{var _G0=E(_FW.b),_G1=E(_FX.b);if(_G0>=_G1){if(_G0!=_G1){return true;}else{var _G2=E(_FW.c),_G3=E(_FX.c);if(_G2>=_G3){if(_G2!=_G3){return true;}else{return new F(function(){return _FC(_FS,_FV);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_G4=function(_G5,_G6){var _G7=E(_G5),_G8=E(_G6);return new F(function(){return _FP(E(_G7.a),_G7.b,_G7.c,E(_G8.a),_G8.b,_G8.c);});},_G9=function(_Ga,_Gb,_Gc,_Gd,_Ge,_Gf,_Gg,_Gh,_Gi,_Gj,_Gk,_Gl,_Gm,_Gn,_Go,_Gp,_Gq,_Gr,_Gs,_Gt,_Gu,_Gv,_Gw,_Gx){if(_Ga>=_Gm){if(_Ga!=_Gm){return true;}else{if(_Gb>=_Gn){if(_Gb!=_Gn){return true;}else{if(_Gc>=_Go){if(_Gc!=_Go){return true;}else{if(_Gd>=_Gp){if(_Gd!=_Gp){return true;}else{if(_Ge>=_Gq){if(_Ge!=_Gq){return true;}else{if(_Gf>=_Gr){if(_Gf!=_Gr){return true;}else{if(_Gg>=_Gs){if(_Gg!=_Gs){return true;}else{if(_Gh>=_Gt){if(_Gh!=_Gt){return true;}else{if(_Gi>=_Gu){if(_Gi!=_Gu){return true;}else{if(_Gj>=_Gv){if(_Gj!=_Gv){return true;}else{var _Gy=E(_Gk),_Gz=E(_Gw);if(_Gy>=_Gz){if(_Gy!=_Gz){return true;}else{return new F(function(){return _bx(_Gl,_Gx);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_GA=function(_GB,_GC){var _GD=E(_GB),_GE=E(_GD.a),_GF=E(_GD.b),_GG=E(_GD.c),_GH=E(_GD.e),_GI=E(_GC),_GJ=E(_GI.a),_GK=E(_GI.b),_GL=E(_GI.c),_GM=E(_GI.e);return new F(function(){return _G9(_GE.a,_GE.b,_GE.c,_GF.a,_GF.b,_GF.c,_GG.a,_GG.b,_GG.c,_GD.d,_GH.a,_GH.b,_GJ.a,_GJ.b,_GJ.c,_GK.a,_GK.b,_GK.c,_GL.a,_GL.b,_GL.c,_GI.d,_GM.a,_GM.b);});},_GN=function(_GO,_GP,_GQ,_GR,_GS,_GT){if(_GO>=_GR){if(_GO!=_GR){return true;}else{var _GU=E(_GP),_GV=E(_GS),_GW=E(_GU.a),_GX=E(_GV.a);if(_GW>=_GX){if(_GW!=_GX){return true;}else{var _GY=E(_GU.b),_GZ=E(_GV.b);if(_GY>=_GZ){if(_GY!=_GZ){return true;}else{var _H0=E(_GU.c),_H1=E(_GV.c);if(_H0>=_H1){if(_H0!=_H1){return true;}else{return new F(function(){return _GA(_GQ,_GT);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_H2=function(_H3,_H4){var _H5=E(_H3),_H6=E(_H4);return new F(function(){return _GN(E(_H5.a),_H5.b,_H5.c,E(_H6.a),_H6.b,_H6.c);});},_H7=function(_H8,_H9){var _Ha=E(_H8),_Hb=E(_Ha.a),_Hc=E(_H9),_Hd=E(_Hc.a);if(_Hb>=_Hd){if(_Hb!=_Hd){return E(_Ha);}else{var _He=E(_Ha.b),_Hf=E(_Hc.b),_Hg=E(_He.a),_Hh=E(_Hf.a);if(_Hg>=_Hh){if(_Hg!=_Hh){return E(_Ha);}else{var _Hi=E(_He.b),_Hj=E(_Hf.b);if(_Hi>=_Hj){if(_Hi!=_Hj){return E(_Ha);}else{var _Hk=E(_He.c),_Hl=E(_Hf.c);if(_Hk>=_Hl){if(_Hk!=_Hl){return E(_Ha);}else{var _Hm=E(_Ha.c),_Hn=_Hm.d,_Ho=E(_Hm.a),_Hp=_Ho.a,_Hq=_Ho.b,_Hr=_Ho.c,_Hs=E(_Hm.b),_Ht=_Hs.a,_Hu=_Hs.b,_Hv=_Hs.c,_Hw=E(_Hm.c),_Hx=_Hw.a,_Hy=_Hw.b,_Hz=_Hw.c,_HA=E(_Hm.e),_HB=E(_Hc.c),_HC=_HB.d,_HD=E(_HB.a),_HE=_HD.a,_HF=_HD.b,_HG=_HD.c,_HH=E(_HB.b),_HI=_HH.a,_HJ=_HH.b,_HK=_HH.c,_HL=E(_HB.c),_HM=_HL.a,_HN=_HL.b,_HO=_HL.c,_HP=E(_HB.e);if(_Hp>=_HE){if(_Hp!=_HE){return E(_Ha);}else{if(_Hq>=_HF){if(_Hq!=_HF){return E(_Ha);}else{if(_Hr>=_HG){if(_Hr!=_HG){return E(_Ha);}else{if(_Ht>=_HI){if(_Ht!=_HI){return E(_Ha);}else{if(_Hu>=_HJ){if(_Hu!=_HJ){return E(_Ha);}else{if(_Hv>=_HK){if(_Hv!=_HK){return E(_Ha);}else{if(_Hx>=_HM){if(_Hx!=_HM){return E(_Ha);}else{if(_Hy>=_HN){if(_Hy!=_HN){return E(_Ha);}else{if(_Hz>=_HO){if(_Hz!=_HO){return E(_Ha);}else{if(_Hn>=_HC){if(_Hn!=_HC){return E(_Ha);}else{var _HQ=E(_HA.a),_HR=E(_HP.a);return (_HQ>=_HR)?(_HQ!=_HR)?E(_Ha):(E(_HA.b)>E(_HP.b))?E(_Ha):E(_Hc):E(_Hc);}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}}}else{return E(_Hc);}},_HS=function(_HT,_HU){var _HV=E(_HT),_HW=E(_HV.a),_HX=E(_HU),_HY=E(_HX.a);if(_HW>=_HY){if(_HW!=_HY){return E(_HX);}else{var _HZ=E(_HV.b),_I0=E(_HX.b),_I1=E(_HZ.a),_I2=E(_I0.a);if(_I1>=_I2){if(_I1!=_I2){return E(_HX);}else{var _I3=E(_HZ.b),_I4=E(_I0.b);if(_I3>=_I4){if(_I3!=_I4){return E(_HX);}else{var _I5=E(_HZ.c),_I6=E(_I0.c);if(_I5>=_I6){if(_I5!=_I6){return E(_HX);}else{var _I7=E(_HV.c),_I8=_I7.d,_I9=E(_I7.a),_Ia=_I9.a,_Ib=_I9.b,_Ic=_I9.c,_Id=E(_I7.b),_Ie=_Id.a,_If=_Id.b,_Ig=_Id.c,_Ih=E(_I7.c),_Ii=_Ih.a,_Ij=_Ih.b,_Ik=_Ih.c,_Il=E(_I7.e),_Im=E(_HX.c),_In=_Im.d,_Io=E(_Im.a),_Ip=_Io.a,_Iq=_Io.b,_Ir=_Io.c,_Is=E(_Im.b),_It=_Is.a,_Iu=_Is.b,_Iv=_Is.c,_Iw=E(_Im.c),_Ix=_Iw.a,_Iy=_Iw.b,_Iz=_Iw.c,_IA=E(_Im.e);if(_Ia>=_Ip){if(_Ia!=_Ip){return E(_HX);}else{if(_Ib>=_Iq){if(_Ib!=_Iq){return E(_HX);}else{if(_Ic>=_Ir){if(_Ic!=_Ir){return E(_HX);}else{if(_Ie>=_It){if(_Ie!=_It){return E(_HX);}else{if(_If>=_Iu){if(_If!=_Iu){return E(_HX);}else{if(_Ig>=_Iv){if(_Ig!=_Iv){return E(_HX);}else{if(_Ii>=_Ix){if(_Ii!=_Ix){return E(_HX);}else{if(_Ij>=_Iy){if(_Ij!=_Iy){return E(_HX);}else{if(_Ik>=_Iz){if(_Ik!=_Iz){return E(_HX);}else{if(_I8>=_In){if(_I8!=_In){return E(_HX);}else{var _IB=E(_Il.a),_IC=E(_IA.a);return (_IB>=_IC)?(_IB!=_IC)?E(_HX):(E(_Il.b)>E(_IA.b))?E(_HX):E(_HV):E(_HV);}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}}}else{return E(_HV);}},_ID={_:0,a:_Cg,b:_Da,c:_E8,d:_F6,e:_G4,f:_H2,g:_H7,h:_HS},_IE=function(_IF,_IG,_IH,_II){var _IJ=E(_II);if(!_IJ._){var _IK=_IJ.c,_IL=_IJ.d,_IM=_IJ.e,_IN=E(_IJ.b),_IO=E(_IN.a);if(_IF>=_IO){if(_IF!=_IO){return new F(function(){return _xh(_IN,_IK,_IL,B(_IE(_IF,_IG,_IH,_IM)));});}else{var _IP=E(_IN.b);if(_IG>=_IP){if(_IG!=_IP){return new F(function(){return _xh(_IN,_IK,_IL,B(_IE(_IF,_IG,_IH,_IM)));});}else{return new T5(0,_IJ.a,E(new T2(0,_IF,_IG)),_IH,E(_IL),E(_IM));}}else{return new F(function(){return _wA(_IN,_IK,B(_IE(_IF,_IG,_IH,_IL)),_IM);});}}}else{return new F(function(){return _wA(_IN,_IK,B(_IE(_IF,_IG,_IH,_IL)),_IM);});}}else{return new T5(0,1,E(new T2(0,_IF,_IG)),_IH,E(_wv),E(_wv));}},_IQ=new T0(1),_IR=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_IS=function(_IT){return new F(function(){return err(_IR);});},_IU=new T(function(){return B(_IS(_));}),_IV=function(_IW,_IX,_IY){var _IZ=E(_IY);if(!_IZ._){var _J0=_IZ.a,_J1=E(_IX);if(!_J1._){var _J2=_J1.a,_J3=_J1.b;if(_J2<=(imul(3,_J0)|0)){return new T4(0,(1+_J2|0)+_J0|0,E(_IW),E(_J1),E(_IZ));}else{var _J4=E(_J1.c);if(!_J4._){var _J5=_J4.a,_J6=E(_J1.d);if(!_J6._){var _J7=_J6.a,_J8=_J6.b,_J9=_J6.c;if(_J7>=(imul(2,_J5)|0)){var _Ja=function(_Jb){var _Jc=E(_J6.d);return (_Jc._==0)?new T4(0,(1+_J2|0)+_J0|0,E(_J8),E(new T4(0,(1+_J5|0)+_Jb|0,E(_J3),E(_J4),E(_J9))),E(new T4(0,(1+_J0|0)+_Jc.a|0,E(_IW),E(_Jc),E(_IZ)))):new T4(0,(1+_J2|0)+_J0|0,E(_J8),E(new T4(0,(1+_J5|0)+_Jb|0,E(_J3),E(_J4),E(_J9))),E(new T4(0,1+_J0|0,E(_IW),E(_IQ),E(_IZ))));},_Jd=E(_J9);if(!_Jd._){return new F(function(){return _Ja(_Jd.a);});}else{return new F(function(){return _Ja(0);});}}else{return new T4(0,(1+_J2|0)+_J0|0,E(_J3),E(_J4),E(new T4(0,(1+_J0|0)+_J7|0,E(_IW),E(_J6),E(_IZ))));}}else{return E(_IU);}}else{return E(_IU);}}}else{return new T4(0,1+_J0|0,E(_IW),E(_IQ),E(_IZ));}}else{var _Je=E(_IX);if(!_Je._){var _Jf=_Je.a,_Jg=_Je.b,_Jh=_Je.d,_Ji=E(_Je.c);if(!_Ji._){var _Jj=_Ji.a,_Jk=E(_Jh);if(!_Jk._){var _Jl=_Jk.a,_Jm=_Jk.b,_Jn=_Jk.c;if(_Jl>=(imul(2,_Jj)|0)){var _Jo=function(_Jp){var _Jq=E(_Jk.d);return (_Jq._==0)?new T4(0,1+_Jf|0,E(_Jm),E(new T4(0,(1+_Jj|0)+_Jp|0,E(_Jg),E(_Ji),E(_Jn))),E(new T4(0,1+_Jq.a|0,E(_IW),E(_Jq),E(_IQ)))):new T4(0,1+_Jf|0,E(_Jm),E(new T4(0,(1+_Jj|0)+_Jp|0,E(_Jg),E(_Ji),E(_Jn))),E(new T4(0,1,E(_IW),E(_IQ),E(_IQ))));},_Jr=E(_Jn);if(!_Jr._){return new F(function(){return _Jo(_Jr.a);});}else{return new F(function(){return _Jo(0);});}}else{return new T4(0,1+_Jf|0,E(_Jg),E(_Ji),E(new T4(0,1+_Jl|0,E(_IW),E(_Jk),E(_IQ))));}}else{return new T4(0,3,E(_Jg),E(_Ji),E(new T4(0,1,E(_IW),E(_IQ),E(_IQ))));}}else{var _Js=E(_Jh);return (_Js._==0)?new T4(0,3,E(_Js.b),E(new T4(0,1,E(_Jg),E(_IQ),E(_IQ))),E(new T4(0,1,E(_IW),E(_IQ),E(_IQ)))):new T4(0,2,E(_IW),E(_Je),E(_IQ));}}else{return new T4(0,1,E(_IW),E(_IQ),E(_IQ));}}},_Jt=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Ju=function(_Jv){return new F(function(){return err(_Jt);});},_Jw=new T(function(){return B(_Ju(_));}),_Jx=function(_Jy,_Jz,_JA){var _JB=E(_Jz);if(!_JB._){var _JC=_JB.a,_JD=E(_JA);if(!_JD._){var _JE=_JD.a,_JF=_JD.b;if(_JE<=(imul(3,_JC)|0)){return new T4(0,(1+_JC|0)+_JE|0,E(_Jy),E(_JB),E(_JD));}else{var _JG=E(_JD.c);if(!_JG._){var _JH=_JG.a,_JI=_JG.b,_JJ=_JG.c,_JK=E(_JD.d);if(!_JK._){var _JL=_JK.a;if(_JH>=(imul(2,_JL)|0)){var _JM=function(_JN){var _JO=E(_Jy),_JP=E(_JG.d);return (_JP._==0)?new T4(0,(1+_JC|0)+_JE|0,E(_JI),E(new T4(0,(1+_JC|0)+_JN|0,E(_JO),E(_JB),E(_JJ))),E(new T4(0,(1+_JL|0)+_JP.a|0,E(_JF),E(_JP),E(_JK)))):new T4(0,(1+_JC|0)+_JE|0,E(_JI),E(new T4(0,(1+_JC|0)+_JN|0,E(_JO),E(_JB),E(_JJ))),E(new T4(0,1+_JL|0,E(_JF),E(_IQ),E(_JK))));},_JQ=E(_JJ);if(!_JQ._){return new F(function(){return _JM(_JQ.a);});}else{return new F(function(){return _JM(0);});}}else{return new T4(0,(1+_JC|0)+_JE|0,E(_JF),E(new T4(0,(1+_JC|0)+_JH|0,E(_Jy),E(_JB),E(_JG))),E(_JK));}}else{return E(_Jw);}}else{return E(_Jw);}}}else{return new T4(0,1+_JC|0,E(_Jy),E(_JB),E(_IQ));}}else{var _JR=E(_JA);if(!_JR._){var _JS=_JR.a,_JT=_JR.b,_JU=_JR.d,_JV=E(_JR.c);if(!_JV._){var _JW=_JV.a,_JX=_JV.b,_JY=_JV.c,_JZ=E(_JU);if(!_JZ._){var _K0=_JZ.a;if(_JW>=(imul(2,_K0)|0)){var _K1=function(_K2){var _K3=E(_Jy),_K4=E(_JV.d);return (_K4._==0)?new T4(0,1+_JS|0,E(_JX),E(new T4(0,1+_K2|0,E(_K3),E(_IQ),E(_JY))),E(new T4(0,(1+_K0|0)+_K4.a|0,E(_JT),E(_K4),E(_JZ)))):new T4(0,1+_JS|0,E(_JX),E(new T4(0,1+_K2|0,E(_K3),E(_IQ),E(_JY))),E(new T4(0,1+_K0|0,E(_JT),E(_IQ),E(_JZ))));},_K5=E(_JY);if(!_K5._){return new F(function(){return _K1(_K5.a);});}else{return new F(function(){return _K1(0);});}}else{return new T4(0,1+_JS|0,E(_JT),E(new T4(0,1+_JW|0,E(_Jy),E(_IQ),E(_JV))),E(_JZ));}}else{return new T4(0,3,E(_JX),E(new T4(0,1,E(_Jy),E(_IQ),E(_IQ))),E(new T4(0,1,E(_JT),E(_IQ),E(_IQ))));}}else{var _K6=E(_JU);return (_K6._==0)?new T4(0,3,E(_JT),E(new T4(0,1,E(_Jy),E(_IQ),E(_IQ))),E(_K6)):new T4(0,2,E(_Jy),E(_IQ),E(_JR));}}else{return new T4(0,1,E(_Jy),E(_IQ),E(_IQ));}}},_K7=function(_K8,_K9,_Ka){var _Kb=E(_K9),_Kc=E(_Ka);if(!_Kc._){var _Kd=_Kc.b,_Ke=_Kc.c,_Kf=_Kc.d;switch(B(A3(_wt,_K8,_Kb,_Kd))){case 0:return new F(function(){return _IV(_Kd,B(_K7(_K8,_Kb,_Ke)),_Kf);});break;case 1:return new T4(0,_Kc.a,E(_Kb),E(_Ke),E(_Kf));default:return new F(function(){return _Jx(_Kd,_Ke,B(_K7(_K8,_Kb,_Kf)));});}}else{return new T4(0,1,E(_Kb),E(_IQ),E(_IQ));}},_Kg=function(_Kh,_Ki,_Kj,_Kk,_Kl){var _Km=E(_Kl);if(!_Km._){var _Kn=new T(function(){var _Ko=B(_Kg(_Km.a,_Km.b,_Km.c,_Km.d,_Km.e));return new T2(0,_Ko.a,_Ko.b);});return new T2(0,new T(function(){return E(E(_Kn).a);}),new T(function(){return B(_wA(_Ki,_Kj,_Kk,E(_Kn).b));}));}else{return new T2(0,new T2(0,_Ki,_Kj),_Kk);}},_Kp=function(_Kq,_Kr,_Ks,_Kt,_Ku){var _Kv=E(_Kt);if(!_Kv._){var _Kw=new T(function(){var _Kx=B(_Kp(_Kv.a,_Kv.b,_Kv.c,_Kv.d,_Kv.e));return new T2(0,_Kx.a,_Kx.b);});return new T2(0,new T(function(){return E(E(_Kw).a);}),new T(function(){return B(_xh(_Kr,_Ks,E(_Kw).b,_Ku));}));}else{return new T2(0,new T2(0,_Kr,_Ks),_Ku);}},_Ky=function(_Kz,_KA){var _KB=E(_Kz);if(!_KB._){var _KC=_KB.a,_KD=E(_KA);if(!_KD._){var _KE=_KD.a;if(_KC<=_KE){var _KF=B(_Kp(_KE,_KD.b,_KD.c,_KD.d,_KD.e)),_KG=E(_KF.a);return new F(function(){return _wA(_KG.a,_KG.b,_KB,_KF.b);});}else{var _KH=B(_Kg(_KC,_KB.b,_KB.c,_KB.d,_KB.e)),_KI=E(_KH.a);return new F(function(){return _xh(_KI.a,_KI.b,_KH.b,_KD);});}}else{return E(_KB);}}else{return E(_KA);}},_KJ=function(_KK,_KL,_KM,_KN){var _KO=E(_KN);if(!_KO._){var _KP=_KO.c,_KQ=_KO.d,_KR=_KO.e,_KS=E(_KO.b),_KT=E(_KS.a);if(_KL>=_KT){if(_KL!=_KT){return new F(function(){return _wA(_KS,_KP,_KQ,B(_KJ(_KK,_KL,_KM,_KR)));});}else{var _KU=E(_KS.b);if(_KM>=_KU){if(_KM!=_KU){return new F(function(){return _wA(_KS,_KP,_KQ,B(_KJ(_KK,_KL,_KM,_KR)));});}else{var _KV=B(A2(_KK,_KS,_KP));if(!_KV._){return new F(function(){return _Ky(_KQ,_KR);});}else{return new T5(0,_KO.a,E(_KS),_KV.a,E(_KQ),E(_KR));}}}else{return new F(function(){return _xh(_KS,_KP,B(_KJ(_KK,_KL,_KM,_KQ)),_KR);});}}}else{return new F(function(){return _xh(_KS,_KP,B(_KJ(_KK,_KL,_KM,_KQ)),_KR);});}}else{return new T0(1);}},_KW=function(_KX,_KY,_KZ,_L0){var _L1=E(_L0);if(!_L1._){var _L2=_L1.c,_L3=_L1.d,_L4=_L1.e,_L5=E(_L1.b),_L6=E(_L5.a);if(_KY>=_L6){if(_KY!=_L6){return new F(function(){return _wA(_L5,_L2,_L3,B(_KW(_KX,_KY,_KZ,_L4)));});}else{var _L7=E(_KZ),_L8=E(_L5.b);if(_L7>=_L8){if(_L7!=_L8){return new F(function(){return _wA(_L5,_L2,_L3,B(_KJ(_KX,_KY,_L7,_L4)));});}else{var _L9=B(A2(_KX,_L5,_L2));if(!_L9._){return new F(function(){return _Ky(_L3,_L4);});}else{return new T5(0,_L1.a,E(_L5),_L9.a,E(_L3),E(_L4));}}}else{return new F(function(){return _xh(_L5,_L2,B(_KJ(_KX,_KY,_L7,_L3)),_L4);});}}}else{return new F(function(){return _xh(_L5,_L2,B(_KW(_KX,_KY,_KZ,_L3)),_L4);});}}else{return new T0(1);}},_La=function(_Lb,_Lc,_Ld,_Le){var _Lf=E(_Le);if(!_Lf._){var _Lg=_Lf.c,_Lh=_Lf.d,_Li=_Lf.e,_Lj=E(_Lf.b),_Lk=E(_Lc),_Ll=E(_Lj.a);if(_Lk>=_Ll){if(_Lk!=_Ll){return new F(function(){return _wA(_Lj,_Lg,_Lh,B(_KW(_Lb,_Lk,_Ld,_Li)));});}else{var _Lm=E(_Ld),_Ln=E(_Lj.b);if(_Lm>=_Ln){if(_Lm!=_Ln){return new F(function(){return _wA(_Lj,_Lg,_Lh,B(_KJ(_Lb,_Lk,_Lm,_Li)));});}else{var _Lo=B(A2(_Lb,_Lj,_Lg));if(!_Lo._){return new F(function(){return _Ky(_Lh,_Li);});}else{return new T5(0,_Lf.a,E(_Lj),_Lo.a,E(_Lh),E(_Li));}}}else{return new F(function(){return _xh(_Lj,_Lg,B(_KJ(_Lb,_Lk,_Lm,_Lh)),_Li);});}}}else{return new F(function(){return _xh(_Lj,_Lg,B(_KW(_Lb,_Lk,_Ld,_Lh)),_Li);});}}else{return new T0(1);}},_Lp=function(_Lq,_Lr,_Ls,_Lt,_Lu,_Lv,_Lw,_Lx,_Ly,_Lz){var _LA=_Ly-_Ls,_LB=_Lz-_Lt,_LC=_Lv-_Ls,_LD=_Lw-_Lt,_LE=_LC*_LB-_LD*_LA+(_LC*_LB-_LD*_LA);return (_LE>0)?new T1(1,new T(function(){var _LF=_LA*_LA+_LB*_LB,_LG=_LC*_LC+_LD*_LD,_LH=E(_Lq),_LI=_Ls+(_LB*_LG-_LD*_LF)/_LE,_LJ=_Lt+(_LC*_LF-_LA*_LG)/_LE,_LK=_LJ+Math.sqrt((_LI-_Ls)*(_LI-_Ls)+(_LJ-_Lt)*(_LJ-_Lt));if(_LK>_LH){return new T5(0,E(new T3(0,_Lr,_Ls,_Lt)),E(new T3(0,_Lu,_Lv,_Lw)),E(new T3(0,_Lx,_Ly,_Lz)),_LH,E(new T2(0,_LI,_LJ)));}else{return new T5(0,E(new T3(0,_Lr,_Ls,_Lt)),E(new T3(0,_Lu,_Lv,_Lw)),E(new T3(0,_Lx,_Ly,_Lz)),_LK,E(new T2(0,_LI,_LJ)));}})):__Z;},_LL=function(_LM,_LN,_LO){while(1){var _LP=E(_LM);if(!_LP._){return E(_LN);}else{_LM=_LP.a;_LN=_LP.b;_LO=_LP.c;continue;}}},_LQ=function(_LR,_LS,_LT){var _LU=E(_LR);return (_LU._==0)?E(_LT):new T3(1,new T(function(){return B(_LQ(_LU.a,_LU.b,_LU.c));}),_LS,_LT);},_LV=new T(function(){return B(_84("Fortune/BreakpointTree.hs:(154,1)-(163,30)|function delete"));}),_LW=new T(function(){return B(unCStr("delete: Reached Nil"));}),_LX=new T(function(){return B(err(_LW));}),_LY=function(_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M6){var _M7=E(_M6);if(!_M7._){return E(_LX);}else{var _M8=_M7.a,_M9=_M7.c,_Ma=E(_M7.b),_Mb=E(_Ma.a),_Mc=_Mb.b,_Md=_Mb.c,_Me=E(_Ma.b),_Mf=_Me.b,_Mg=_Me.c,_Mh=function(_Mi){var _Mj=_M1-_M4,_Mk=function(_Ml){var _Mm=_Md-_Mg,_Mn=function(_Mo){return (_Ml>=_Mo)?(_Ml<_Mo)?E(_LV):new T3(1,_M8,_Ma,new T(function(){return B(_LY(_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M9));})):new T3(1,new T(function(){return B(_LY(_LZ,_M0,_M1,_M2,_M3,_M4,_M5,_M8));}),_Ma,_M9);};if(_Mm!=0){if(_Mm<=0){if( -_Mm>=1.0e-7){var _Mp=E(_M5);return new F(function(){return _Mn((_Md*_Mf+Math.sqrt(((_Mc-_Mf)*(_Mc-_Mf)+_Mm*_Mm)*(_Md-_Mp)*(_Mg-_Mp))+(_Mc*(_Mp-_Mg)-_Mf*_Mp))/_Mm);});}else{return new F(function(){return _Mn((_Mc+_Mf)/2);});}}else{if(_Mm>=1.0e-7){var _Mq=E(_M5);return new F(function(){return _Mn((_Md*_Mf+Math.sqrt(((_Mc-_Mf)*(_Mc-_Mf)+_Mm*_Mm)*(_Md-_Mq)*(_Mg-_Mq))+(_Mc*(_Mq-_Mg)-_Mf*_Mq))/_Mm);});}else{return new F(function(){return _Mn((_Mc+_Mf)/2);});}}}else{return new F(function(){return _Mn((_Mc+_Mf)/2);});}};if(_Mj!=0){if(_Mj<=0){if( -_Mj>=1.0e-7){var _Mr=E(_M5);return new F(function(){return _Mk((_M1*_M3+Math.sqrt(((_M0-_M3)*(_M0-_M3)+_Mj*_Mj)*(_M1-_Mr)*(_M4-_Mr))+(_M0*(_Mr-_M4)-_M3*_Mr))/_Mj);});}else{return new F(function(){return _Mk((_M0+_M3)/2);});}}else{if(_Mj>=1.0e-7){var _Ms=E(_M5);return new F(function(){return _Mk((_M1*_M3+Math.sqrt(((_M0-_M3)*(_M0-_M3)+_Mj*_Mj)*(_M1-_Ms)*(_M4-_Ms))+(_M0*(_Ms-_M4)-_M3*_Ms))/_Mj);});}else{return new F(function(){return _Mk((_M0+_M3)/2);});}}}else{return new F(function(){return _Mk((_M0+_M3)/2);});}};if(_Mb.a!=_LZ){return new F(function(){return _Mh(_);});}else{if(_Me.a!=_M2){return new F(function(){return _Mh(_);});}else{var _Mt=E(_M8);if(!_Mt._){return E(_M9);}else{var _Mu=E(_M9);if(!_Mu._){return E(_Mt);}else{var _Mv=_Mu.a,_Mw=_Mu.b,_Mx=_Mu.c;return new T3(1,_Mt,new T(function(){return B(_LL(_Mv,_Mw,_Mx));}),new T(function(){return B(_LQ(_Mv,_Mw,_Mx));}));}}}}}},_My=function(_Mz,_MA,_MB,_MC,_MD,_ME,_MF,_MG,_MH,_MI){var _MJ=E(_MH),_MK=E(_MJ.a),_ML=_MK.b,_MM=_MK.c,_MN=E(_MJ.b),_MO=_MN.b,_MP=_MN.c,_MQ=function(_MR){var _MS=_MB-_ME,_MT=function(_MU){var _MV=_MM-_MP,_MW=function(_MX){return (_MU>=_MX)?(_MU<_MX)?E(_LV):new T3(1,_MG,_MJ,new T(function(){return B(_LY(_Mz,_MA,_MB,_MC,_MD,_ME,_MF,_MI));})):new T3(1,new T(function(){return B(_LY(_Mz,_MA,_MB,_MC,_MD,_ME,_MF,_MG));}),_MJ,_MI);};if(_MV!=0){if(_MV<=0){if( -_MV>=1.0e-7){var _MY=E(_MF);return new F(function(){return _MW((_MM*_MO+Math.sqrt(((_ML-_MO)*(_ML-_MO)+_MV*_MV)*(_MM-_MY)*(_MP-_MY))+(_ML*(_MY-_MP)-_MO*_MY))/_MV);});}else{return new F(function(){return _MW((_ML+_MO)/2);});}}else{if(_MV>=1.0e-7){var _MZ=E(_MF);return new F(function(){return _MW((_MM*_MO+Math.sqrt(((_ML-_MO)*(_ML-_MO)+_MV*_MV)*(_MM-_MZ)*(_MP-_MZ))+(_ML*(_MZ-_MP)-_MO*_MZ))/_MV);});}else{return new F(function(){return _MW((_ML+_MO)/2);});}}}else{return new F(function(){return _MW((_ML+_MO)/2);});}};if(_MS!=0){if(_MS<=0){if( -_MS>=1.0e-7){var _N0=E(_MF);return new F(function(){return _MT((_MB*_MD+Math.sqrt(((_MA-_MD)*(_MA-_MD)+_MS*_MS)*(_MB-_N0)*(_ME-_N0))+(_MA*(_N0-_ME)-_MD*_N0))/_MS);});}else{return new F(function(){return _MT((_MA+_MD)/2);});}}else{if(_MS>=1.0e-7){var _N1=E(_MF);return new F(function(){return _MT((_MB*_MD+Math.sqrt(((_MA-_MD)*(_MA-_MD)+_MS*_MS)*(_MB-_N1)*(_ME-_N1))+(_MA*(_N1-_ME)-_MD*_N1))/_MS);});}else{return new F(function(){return _MT((_MA+_MD)/2);});}}}else{return new F(function(){return _MT((_MA+_MD)/2);});}};if(_MK.a!=_Mz){return new F(function(){return _MQ(_);});}else{if(_MN.a!=_MC){return new F(function(){return _MQ(_);});}else{var _N2=E(_MG);if(!_N2._){return E(_MI);}else{var _N3=E(_MI);if(!_N3._){return E(_N2);}else{var _N4=_N3.a,_N5=_N3.b,_N6=_N3.c;return new T3(1,_N2,new T(function(){return B(_LL(_N4,_N5,_N6));}),new T(function(){return B(_LQ(_N4,_N5,_N6));}));}}}}},_N7=function(_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh,_Ni,_Nj){var _Nk=E(_Ni),_Nl=E(_Nk.a),_Nm=_Nl.b,_Nn=_Nl.c,_No=E(_Nk.b),_Np=_No.b,_Nq=_No.c,_Nr=function(_Ns){var _Nt=_Na-_Nd,_Nu=function(_Nv){var _Nw=_Nn-_Nq,_Nx=function(_Ny){return (_Nv>=_Ny)?(_Nv<_Ny)?E(_LV):new T3(1,new T3(1,_Nf,_Ng,_Nh),_Nk,new T(function(){return B(_LY(_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne,_Nj));})):new T3(1,new T(function(){return B(_My(_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne,_Nf,_Ng,_Nh));}),_Nk,_Nj);};if(_Nw!=0){if(_Nw<=0){if( -_Nw>=1.0e-7){var _Nz=E(_Ne);return new F(function(){return _Nx((_Nn*_Np+Math.sqrt(((_Nm-_Np)*(_Nm-_Np)+_Nw*_Nw)*(_Nn-_Nz)*(_Nq-_Nz))+(_Nm*(_Nz-_Nq)-_Np*_Nz))/_Nw);});}else{return new F(function(){return _Nx((_Nm+_Np)/2);});}}else{if(_Nw>=1.0e-7){var _NA=E(_Ne);return new F(function(){return _Nx((_Nn*_Np+Math.sqrt(((_Nm-_Np)*(_Nm-_Np)+_Nw*_Nw)*(_Nn-_NA)*(_Nq-_NA))+(_Nm*(_NA-_Nq)-_Np*_NA))/_Nw);});}else{return new F(function(){return _Nx((_Nm+_Np)/2);});}}}else{return new F(function(){return _Nx((_Nm+_Np)/2);});}};if(_Nt!=0){if(_Nt<=0){if( -_Nt>=1.0e-7){var _NB=E(_Ne);return new F(function(){return _Nu((_Na*_Nc+Math.sqrt(((_N9-_Nc)*(_N9-_Nc)+_Nt*_Nt)*(_Na-_NB)*(_Nd-_NB))+(_N9*(_NB-_Nd)-_Nc*_NB))/_Nt);});}else{return new F(function(){return _Nu((_N9+_Nc)/2);});}}else{if(_Nt>=1.0e-7){var _NC=E(_Ne);return new F(function(){return _Nu((_Na*_Nc+Math.sqrt(((_N9-_Nc)*(_N9-_Nc)+_Nt*_Nt)*(_Na-_NC)*(_Nd-_NC))+(_N9*(_NC-_Nd)-_Nc*_NC))/_Nt);});}else{return new F(function(){return _Nu((_N9+_Nc)/2);});}}}else{return new F(function(){return _Nu((_N9+_Nc)/2);});}};if(_Nl.a!=_N8){return new F(function(){return _Nr(_);});}else{if(_No.a!=_Nb){return new F(function(){return _Nr(_);});}else{var _ND=E(_Nj);if(!_ND._){return new T3(1,_Nf,_Ng,_Nh);}else{var _NE=_ND.a,_NF=_ND.b,_NG=_ND.c;return new T3(1,new T3(1,_Nf,_Ng,_Nh),new T(function(){return B(_LL(_NE,_NF,_NG));}),new T(function(){return B(_LQ(_NE,_NF,_NG));}));}}}},_NH=function(_NI,_NJ,_NK,_NL,_NM){var _NN=_NJ-_NL;if(_NN!=0){if(_NN<=0){if( -_NN>=1.0e-7){var _NO=E(_NM);return (_NJ*_NK+Math.sqrt(((_NI-_NK)*(_NI-_NK)+_NN*_NN)*(_NJ-_NO)*(_NL-_NO))+(_NI*(_NO-_NL)-_NK*_NO))/_NN;}else{return (_NI+_NK)/2;}}else{if(_NN>=1.0e-7){var _NP=E(_NM);return (_NJ*_NK+Math.sqrt(((_NI-_NK)*(_NI-_NK)+_NN*_NN)*(_NJ-_NP)*(_NL-_NP))+(_NI*(_NP-_NL)-_NK*_NP))/_NN;}else{return (_NI+_NK)/2;}}}else{return (_NI+_NK)/2;}},_NQ=new T(function(){return B(unCStr("delete2: reached nil."));}),_NR=new T(function(){return B(err(_NQ));}),_NS=function(_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O6){var _O7=E(_O6);if(!_O7._){return E(_NR);}else{var _O8=_O7.a,_O9=_O7.c,_Oa=E(_O7.b),_Ob=E(_Oa.a),_Oc=_Ob.a,_Od=_Ob.b,_Oe=_Ob.c,_Of=E(_Oa.b),_Og=_Of.a,_Oh=_Of.b,_Oi=_Of.c,_Oj=function(_Ok){var _Ol=function(_Om){var _On=_NV-_NY,_Oo=function(_Op){var _Oq=_Oe-_Oi,_Or=function(_Os){var _Ot=new T(function(){return B(_NH(_O0,_O1,_O3,_O4,_O5));}),_Ou=function(_Ov){var _Ow=function(_Ox){return (_Op>=_Os)?new T3(1,new T(function(){return B(_LY(_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O8));}),_Oa,new T(function(){return B(_LY(_NT,_NU,_NV,_NW,_NX,_NY,_O5,_O9));})):new T3(1,new T(function(){return B(_LY(_NT,_NU,_NV,_NW,_NX,_NY,_O5,_O8));}),_Oa,new T(function(){return B(_LY(_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O9));}));};if(_Op<_Os){return new F(function(){return _Ow(_);});}else{if(E(_Ot)<_Os){return new F(function(){return _Ow(_);});}else{return new T3(1,_O8,_Oa,new T(function(){return B(_NS(_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O9));}));}}};if(_Op>=_Os){return new F(function(){return _Ou(_);});}else{if(E(_Ot)>=_Os){return new F(function(){return _Ou(_);});}else{return new T3(1,new T(function(){return B(_NS(_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O8));}),_Oa,_O9);}}};if(_Oq!=0){if(_Oq<=0){if( -_Oq>=1.0e-7){var _Oy=E(_O5);return new F(function(){return _Or((_Oe*_Oh+Math.sqrt(((_Od-_Oh)*(_Od-_Oh)+_Oq*_Oq)*(_Oe-_Oy)*(_Oi-_Oy))+(_Od*(_Oy-_Oi)-_Oh*_Oy))/_Oq);});}else{return new F(function(){return _Or((_Od+_Oh)/2);});}}else{if(_Oq>=1.0e-7){var _Oz=E(_O5);return new F(function(){return _Or((_Oe*_Oh+Math.sqrt(((_Od-_Oh)*(_Od-_Oh)+_Oq*_Oq)*(_Oe-_Oz)*(_Oi-_Oz))+(_Od*(_Oz-_Oi)-_Oh*_Oz))/_Oq);});}else{return new F(function(){return _Or((_Od+_Oh)/2);});}}}else{return new F(function(){return _Or((_Od+_Oh)/2);});}};if(_On!=0){if(_On<=0){if( -_On>=1.0e-7){var _OA=E(_O5);return new F(function(){return _Oo((_NV*_NX+Math.sqrt(((_NU-_NX)*(_NU-_NX)+_On*_On)*(_NV-_OA)*(_NY-_OA))+(_NU*(_OA-_NY)-_NX*_OA))/_On);});}else{return new F(function(){return _Oo((_NU+_NX)/2);});}}else{if(_On>=1.0e-7){var _OB=E(_O5);return new F(function(){return _Oo((_NV*_NX+Math.sqrt(((_NU-_NX)*(_NU-_NX)+_On*_On)*(_NV-_OB)*(_NY-_OB))+(_NU*(_OB-_NY)-_NX*_OB))/_On);});}else{return new F(function(){return _Oo((_NU+_NX)/2);});}}}else{return new F(function(){return _Oo((_NU+_NX)/2);});}};if(_NZ!=_Oc){return new F(function(){return _Ol(_);});}else{if(_O2!=_Og){return new F(function(){return _Ol(_);});}else{var _OC=E(_O8);if(!_OC._){return new F(function(){return _LY(_NT,_NU,_NV,_NW,_NX,_NY,_O5,_O9);});}else{var _OD=_OC.a,_OE=_OC.b,_OF=_OC.c,_OG=E(_O9);if(!_OG._){return new F(function(){return _My(_NT,_NU,_NV,_NW,_NX,_NY,_O5,_OD,_OE,_OF);});}else{var _OH=_OG.a,_OI=_OG.b,_OJ=_OG.c;return new F(function(){return _N7(_NT,_NU,_NV,_NW,_NX,_NY,_O5,_OD,_OE,_OF,new T(function(){return B(_LL(_OH,_OI,_OJ));}),new T(function(){return B(_LQ(_OH,_OI,_OJ));}));});}}}}};if(_NT!=_Oc){return new F(function(){return _Oj(_);});}else{if(_NW!=_Og){return new F(function(){return _Oj(_);});}else{var _OK=E(_O8);if(!_OK._){return new F(function(){return _LY(_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_O9);});}else{var _OL=_OK.a,_OM=_OK.b,_ON=_OK.c,_OO=E(_O9);if(!_OO._){return new F(function(){return _My(_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_OL,_OM,_ON);});}else{var _OP=_OO.a,_OQ=_OO.b,_OR=_OO.c;return new F(function(){return _N7(_NZ,_O0,_O1,_O2,_O3,_O4,_O5,_OL,_OM,_ON,new T(function(){return B(_LL(_OP,_OQ,_OR));}),new T(function(){return B(_LQ(_OP,_OQ,_OR));}));});}}}}}},_OS=__Z,_OT=new T(function(){return B(unCStr("insertPar: Cannot insert into empty tree."));}),_OU=new T(function(){return B(err(_OT));}),_OV=function(_OW,_OX,_OY,_OZ,_P0){var _P1=E(_P0);if(!_P1._){return E(_OU);}else{var _P2=_P1.b,_P3=_P1.c,_P4=new T3(0,_OW,_OX,_OY),_P5=E(_P1.a);if(!_P5._){var _P6=E(_P3);if(!_P6._){var _P7=E(_P2),_P8=E(_P7.a),_P9=_P8.b,_Pa=_P8.c,_Pb=E(_P7.b),_Pc=_Pb.b,_Pd=_Pb.c,_Pe=_Pa-_Pd,_Pf=function(_Pg){return (_OX>=_Pg)?new T2(0,new T3(1,_OS,_P7,new T3(1,_OS,new T2(0,E(_Pb),E(_P4)),new T3(1,_OS,new T2(0,E(_P4),E(_Pb)),_OS))),new T1(1,_P7)):new T2(0,new T3(1,new T3(1,_OS,new T2(0,E(_P8),E(_P4)),new T3(1,_OS,new T2(0,E(_P4),E(_P8)),_OS)),_P7,_OS),new T1(0,_P7));};if(_Pe!=0){if(_Pe<=0){if( -_Pe>=1.0e-7){var _Ph=E(_OZ);return new F(function(){return _Pf((_Pa*_Pc+Math.sqrt(((_P9-_Pc)*(_P9-_Pc)+_Pe*_Pe)*(_Pa-_Ph)*(_Pd-_Ph))+(_P9*(_Ph-_Pd)-_Pc*_Ph))/_Pe);});}else{return new F(function(){return _Pf((_P9+_Pc)/2);});}}else{if(_Pe>=1.0e-7){var _Pi=E(_OZ);return new F(function(){return _Pf((_Pa*_Pc+Math.sqrt(((_P9-_Pc)*(_P9-_Pc)+_Pe*_Pe)*(_Pa-_Pi)*(_Pd-_Pi))+(_P9*(_Pi-_Pd)-_Pc*_Pi))/_Pe);});}else{return new F(function(){return _Pf((_P9+_Pc)/2);});}}}else{return new F(function(){return _Pf((_P9+_Pc)/2);});}}else{var _Pj=E(_P2),_Pk=E(_Pj.a),_Pl=_Pk.b,_Pm=_Pk.c,_Pn=E(_Pj.b),_Po=_Pn.b,_Pp=_Pn.c,_Pq=_Pm-_Pp,_Pr=function(_Ps){if(_OX>=_Ps){var _Pt=new T(function(){var _Pu=B(_OV(_OW,_OX,_OY,_OZ,_P6));return new T2(0,_Pu.a,_Pu.b);});return new T2(0,new T3(1,_OS,_Pj,new T(function(){return E(E(_Pt).a);})),new T(function(){return E(E(_Pt).b);}));}else{return new T2(0,new T3(1,new T3(1,_OS,new T2(0,E(_Pk),E(_P4)),new T3(1,_OS,new T2(0,E(_P4),E(_Pk)),_OS)),_Pj,_P6),new T1(0,_Pj));}};if(_Pq!=0){if(_Pq<=0){if( -_Pq>=1.0e-7){var _Pv=E(_OZ);return new F(function(){return _Pr((_Pm*_Po+Math.sqrt(((_Pl-_Po)*(_Pl-_Po)+_Pq*_Pq)*(_Pm-_Pv)*(_Pp-_Pv))+(_Pl*(_Pv-_Pp)-_Po*_Pv))/_Pq);});}else{return new F(function(){return _Pr((_Pl+_Po)/2);});}}else{if(_Pq>=1.0e-7){var _Pw=E(_OZ);return new F(function(){return _Pr((_Pm*_Po+Math.sqrt(((_Pl-_Po)*(_Pl-_Po)+_Pq*_Pq)*(_Pm-_Pw)*(_Pp-_Pw))+(_Pl*(_Pw-_Pp)-_Po*_Pw))/_Pq);});}else{return new F(function(){return _Pr((_Pl+_Po)/2);});}}}else{return new F(function(){return _Pr((_Pl+_Po)/2);});}}}else{var _Px=E(_P3);if(!_Px._){var _Py=E(_P2),_Pz=E(_Py.b),_PA=_Pz.b,_PB=_Pz.c,_PC=E(_Py.a),_PD=_PC.b,_PE=_PC.c,_PF=_PE-_PB,_PG=function(_PH){if(_OX>=_PH){return new T2(0,new T3(1,_P5,_Py,new T3(1,_OS,new T2(0,E(_Pz),E(_P4)),new T3(1,_OS,new T2(0,E(_P4),E(_Pz)),_OS))),new T1(1,_Py));}else{var _PI=new T(function(){var _PJ=B(_OV(_OW,_OX,_OY,_OZ,_P5));return new T2(0,_PJ.a,_PJ.b);});return new T2(0,new T3(1,new T(function(){return E(E(_PI).a);}),_Py,_OS),new T(function(){return E(E(_PI).b);}));}};if(_PF!=0){if(_PF<=0){if( -_PF>=1.0e-7){var _PK=E(_OZ);return new F(function(){return _PG((_PE*_PA+Math.sqrt(((_PD-_PA)*(_PD-_PA)+_PF*_PF)*(_PE-_PK)*(_PB-_PK))+(_PD*(_PK-_PB)-_PA*_PK))/_PF);});}else{return new F(function(){return _PG((_PD+_PA)/2);});}}else{if(_PF>=1.0e-7){var _PL=E(_OZ);return new F(function(){return _PG((_PE*_PA+Math.sqrt(((_PD-_PA)*(_PD-_PA)+_PF*_PF)*(_PE-_PL)*(_PB-_PL))+(_PD*(_PL-_PB)-_PA*_PL))/_PF);});}else{return new F(function(){return _PG((_PD+_PA)/2);});}}}else{return new F(function(){return _PG((_PD+_PA)/2);});}}else{var _PM=E(_P2),_PN=E(_PM.a),_PO=_PN.b,_PP=_PN.c,_PQ=E(_PM.b),_PR=_PQ.b,_PS=_PQ.c,_PT=_PP-_PS,_PU=function(_PV){if(_OX>=_PV){var _PW=new T(function(){var _PX=B(_OV(_OW,_OX,_OY,_OZ,_Px));return new T2(0,_PX.a,_PX.b);});return new T2(0,new T3(1,_P5,_PM,new T(function(){return E(E(_PW).a);})),new T(function(){return E(E(_PW).b);}));}else{var _PY=new T(function(){var _PZ=B(_OV(_OW,_OX,_OY,_OZ,_P5));return new T2(0,_PZ.a,_PZ.b);});return new T2(0,new T3(1,new T(function(){return E(E(_PY).a);}),_PM,_Px),new T(function(){return E(E(_PY).b);}));}};if(_PT!=0){if(_PT<=0){if( -_PT>=1.0e-7){var _Q0=E(_OZ);return new F(function(){return _PU((_PP*_PR+Math.sqrt(((_PO-_PR)*(_PO-_PR)+_PT*_PT)*(_PP-_Q0)*(_PS-_Q0))+(_PO*(_Q0-_PS)-_PR*_Q0))/_PT);});}else{return new F(function(){return _PU((_PO+_PR)/2);});}}else{if(_PT>=1.0e-7){var _Q1=E(_OZ);return new F(function(){return _PU((_PP*_PR+Math.sqrt(((_PO-_PR)*(_PO-_PR)+_PT*_PT)*(_PP-_Q1)*(_PS-_Q1))+(_PO*(_Q1-_PS)-_PR*_Q1))/_PT);});}else{return new F(function(){return _PU((_PO+_PR)/2);});}}}else{return new F(function(){return _PU((_PO+_PR)/2);});}}}}},_Q2=function(_Q3,_Q4){var _Q5=E(_Q4);if(!_Q5._){return __Z;}else{var _Q6=_Q5.a,_Q7=E(_Q3);return (_Q7==1)?new T2(1,_Q6,_6):new T2(1,_Q6,new T(function(){return B(_Q2(_Q7-1|0,_Q5.b));}));}},_Q8=__Z,_Q9=function(_Qa){while(1){var _Qb=B((function(_Qc){var _Qd=E(_Qc);if(!_Qd._){return __Z;}else{var _Qe=_Qd.b,_Qf=E(_Qd.a);if(!_Qf._){_Qa=_Qe;return __continue;}else{return new T2(1,_Qf.a,new T(function(){return B(_Q9(_Qe));}));}}})(_Qa));if(_Qb!=__continue){return _Qb;}}},_Qg=function(_Qh,_Qi,_Qj,_Qk){var _Ql=E(_Qi),_Qm=E(_Qj),_Qn=E(_Qk);return new F(function(){return _Lp(_Qh,_Ql.a,_Ql.b,_Ql.c,_Qm.a,_Qm.b,_Qm.c,_Qn.a,_Qn.b,_Qn.c);});},_Qo=function(_Qp,_Qq,_Qr){while(1){var _Qs=E(_Qr);if(!_Qs._){return false;}else{if(!B(A3(_jA,_Qp,_Qq,_Qs.a))){_Qr=_Qs.b;continue;}else{return true;}}}},_Qt=function(_Qu){return new T4(0,1,E(_Qu),E(_IQ),E(_IQ));},_Qv=function(_Qw,_Qx){var _Qy=E(_Qx);if(!_Qy._){return new F(function(){return _IV(_Qy.b,B(_Qv(_Qw,_Qy.c)),_Qy.d);});}else{return new F(function(){return _Qt(_Qw);});}},_Qz=function(_QA,_QB){var _QC=E(_QB);if(!_QC._){return new F(function(){return _Jx(_QC.b,_QC.c,B(_Qz(_QA,_QC.d)));});}else{return new F(function(){return _Qt(_QA);});}},_QD=function(_QE,_QF,_QG,_QH,_QI){return new F(function(){return _Jx(_QG,_QH,B(_Qz(_QE,_QI)));});},_QJ=function(_QK,_QL,_QM,_QN,_QO){return new F(function(){return _IV(_QM,B(_Qv(_QK,_QN)),_QO);});},_QP=function(_QQ,_QR,_QS,_QT,_QU,_QV){var _QW=E(_QR);if(!_QW._){var _QX=_QW.a,_QY=_QW.b,_QZ=_QW.c,_R0=_QW.d;if((imul(3,_QX)|0)>=_QS){if((imul(3,_QS)|0)>=_QX){return new T4(0,(_QX+_QS|0)+1|0,E(_QQ),E(_QW),E(new T4(0,_QS,E(_QT),E(_QU),E(_QV))));}else{return new F(function(){return _Jx(_QY,_QZ,B(_QP(_QQ,_R0,_QS,_QT,_QU,_QV)));});}}else{return new F(function(){return _IV(_QT,B(_R1(_QQ,_QX,_QY,_QZ,_R0,_QU)),_QV);});}}else{return new F(function(){return _QJ(_QQ,_QS,_QT,_QU,_QV);});}},_R1=function(_R2,_R3,_R4,_R5,_R6,_R7){var _R8=E(_R7);if(!_R8._){var _R9=_R8.a,_Ra=_R8.b,_Rb=_R8.c,_Rc=_R8.d;if((imul(3,_R3)|0)>=_R9){if((imul(3,_R9)|0)>=_R3){return new T4(0,(_R3+_R9|0)+1|0,E(_R2),E(new T4(0,_R3,E(_R4),E(_R5),E(_R6))),E(_R8));}else{return new F(function(){return _Jx(_R4,_R5,B(_QP(_R2,_R6,_R9,_Ra,_Rb,_Rc)));});}}else{return new F(function(){return _IV(_Ra,B(_R1(_R2,_R3,_R4,_R5,_R6,_Rb)),_Rc);});}}else{return new F(function(){return _QD(_R2,_R3,_R4,_R5,_R6);});}},_Rd=function(_Re,_Rf,_Rg){var _Rh=E(_Rf);if(!_Rh._){var _Ri=_Rh.a,_Rj=_Rh.b,_Rk=_Rh.c,_Rl=_Rh.d,_Rm=E(_Rg);if(!_Rm._){var _Rn=_Rm.a,_Ro=_Rm.b,_Rp=_Rm.c,_Rq=_Rm.d;if((imul(3,_Ri)|0)>=_Rn){if((imul(3,_Rn)|0)>=_Ri){return new T4(0,(_Ri+_Rn|0)+1|0,E(_Re),E(_Rh),E(_Rm));}else{return new F(function(){return _Jx(_Rj,_Rk,B(_QP(_Re,_Rl,_Rn,_Ro,_Rp,_Rq)));});}}else{return new F(function(){return _IV(_Ro,B(_R1(_Re,_Ri,_Rj,_Rk,_Rl,_Rp)),_Rq);});}}else{return new F(function(){return _QD(_Re,_Ri,_Rj,_Rk,_Rl);});}}else{return new F(function(){return _Qv(_Re,_Rg);});}},_Rr=function(_Rs,_Rt,_Ru,_Rv){var _Rw=E(_Rv);if(!_Rw._){var _Rx=new T(function(){var _Ry=B(_Rr(_Rw.a,_Rw.b,_Rw.c,_Rw.d));return new T2(0,_Ry.a,_Ry.b);});return new T2(0,new T(function(){return E(E(_Rx).a);}),new T(function(){return B(_IV(_Rt,_Ru,E(_Rx).b));}));}else{return new T2(0,_Rt,_Ru);}},_Rz=function(_RA,_RB,_RC,_RD){var _RE=E(_RC);if(!_RE._){var _RF=new T(function(){var _RG=B(_Rz(_RE.a,_RE.b,_RE.c,_RE.d));return new T2(0,_RG.a,_RG.b);});return new T2(0,new T(function(){return E(E(_RF).a);}),new T(function(){return B(_Jx(_RB,E(_RF).b,_RD));}));}else{return new T2(0,_RB,_RD);}},_RH=function(_RI,_RJ){var _RK=E(_RI);if(!_RK._){var _RL=_RK.a,_RM=E(_RJ);if(!_RM._){var _RN=_RM.a;if(_RL<=_RN){var _RO=B(_Rz(_RN,_RM.b,_RM.c,_RM.d));return new F(function(){return _IV(_RO.a,_RK,_RO.b);});}else{var _RP=B(_Rr(_RL,_RK.b,_RK.c,_RK.d));return new F(function(){return _Jx(_RP.a,_RP.b,_RM);});}}else{return E(_RK);}}else{return E(_RJ);}},_RQ=function(_RR,_RS,_RT,_RU,_RV){var _RW=E(_RR);if(!_RW._){var _RX=_RW.a,_RY=_RW.b,_RZ=_RW.c,_S0=_RW.d;if((imul(3,_RX)|0)>=_RS){if((imul(3,_RS)|0)>=_RX){return new F(function(){return _RH(_RW,new T4(0,_RS,E(_RT),E(_RU),E(_RV)));});}else{return new F(function(){return _Jx(_RY,_RZ,B(_RQ(_S0,_RS,_RT,_RU,_RV)));});}}else{return new F(function(){return _IV(_RT,B(_S1(_RX,_RY,_RZ,_S0,_RU)),_RV);});}}else{return new T4(0,_RS,E(_RT),E(_RU),E(_RV));}},_S1=function(_S2,_S3,_S4,_S5,_S6){var _S7=E(_S6);if(!_S7._){var _S8=_S7.a,_S9=_S7.b,_Sa=_S7.c,_Sb=_S7.d;if((imul(3,_S2)|0)>=_S8){if((imul(3,_S8)|0)>=_S2){return new F(function(){return _RH(new T4(0,_S2,E(_S3),E(_S4),E(_S5)),_S7);});}else{return new F(function(){return _Jx(_S3,_S4,B(_RQ(_S5,_S8,_S9,_Sa,_Sb)));});}}else{return new F(function(){return _IV(_S9,B(_S1(_S2,_S3,_S4,_S5,_Sa)),_Sb);});}}else{return new T4(0,_S2,E(_S3),E(_S4),E(_S5));}},_Sc=function(_Sd,_Se){var _Sf=E(_Sd);if(!_Sf._){var _Sg=_Sf.a,_Sh=_Sf.b,_Si=_Sf.c,_Sj=_Sf.d,_Sk=E(_Se);if(!_Sk._){var _Sl=_Sk.a,_Sm=_Sk.b,_Sn=_Sk.c,_So=_Sk.d;if((imul(3,_Sg)|0)>=_Sl){if((imul(3,_Sl)|0)>=_Sg){return new F(function(){return _RH(_Sf,_Sk);});}else{return new F(function(){return _Jx(_Sh,_Si,B(_RQ(_Sj,_Sl,_Sm,_Sn,_So)));});}}else{return new F(function(){return _IV(_Sm,B(_S1(_Sg,_Sh,_Si,_Sj,_Sn)),_So);});}}else{return E(_Sf);}}else{return E(_Se);}},_Sp=function(_Sq,_Sr){var _Ss=E(_Sr);if(!_Ss._){var _St=_Ss.b,_Su=_Ss.c,_Sv=_Ss.d;if(!B(A1(_Sq,_St))){return new F(function(){return _Sc(B(_Sp(_Sq,_Su)),B(_Sp(_Sq,_Sv)));});}else{return new F(function(){return _Rd(_St,B(_Sp(_Sq,_Su)),B(_Sp(_Sq,_Sv)));});}}else{return new T0(1);}},_Sw=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_Sx=new T(function(){return B(err(_Sw));}),_Sy=function(_Sz,_SA,_SB,_SC){while(1){var _SD=E(_SB);if(!_SD._){_Sz=_SD.a;_SA=_SD.b;_SB=_SD.c;_SC=_SD.d;continue;}else{return E(_SA);}}},_SE=function(_SF,_SG,_SH){return new T3(0,E(_SF),E(_SG),E(_SH));},_SI=function(_SJ,_SK){var _SL=E(_SJ);if(!_SL._){return __Z;}else{var _SM=E(_SK);return (_SM._==0)?__Z:new T2(1,new T(function(){var _SN=E(_SM.a);return B(_SE(_SL.a,_SN.a,_SN.b));}),new T(function(){return B(_SI(_SL.b,_SM.b));}));}},_SO=function(_SP,_SQ,_SR,_SS){var _ST=E(_SS);if(!_ST._){var _SU=_ST.c,_SV=_ST.d,_SW=E(_ST.b),_SX=E(_SP),_SY=E(_SW.a);if(_SX>=_SY){if(_SX!=_SY){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SQ,_SR,_SV)));});}else{var _SZ=E(_SQ),_T0=E(_SW.b),_T1=E(_SZ.a),_T2=E(_T0.a);if(_T1>=_T2){if(_T1!=_T2){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_SR,_SV)));});}else{var _T3=E(_SZ.b),_T4=E(_T0.b);if(_T3>=_T4){if(_T3!=_T4){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_SR,_SV)));});}else{var _T5=E(_SZ.c),_T6=E(_T0.c);if(_T5>=_T6){if(_T5!=_T6){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_SR,_SV)));});}else{var _T7=E(_SR),_T8=_T7.d,_T9=E(_T7.a),_Ta=_T9.a,_Tb=_T9.b,_Tc=_T9.c,_Td=E(_T7.b),_Te=_Td.a,_Tf=_Td.b,_Tg=_Td.c,_Th=E(_T7.c),_Ti=_Th.a,_Tj=_Th.b,_Tk=_Th.c,_Tl=E(_T7.e),_Tm=E(_SW.c),_Tn=_Tm.d,_To=E(_Tm.a),_Tp=_To.a,_Tq=_To.b,_Tr=_To.c,_Ts=E(_Tm.b),_Tt=_Ts.a,_Tu=_Ts.b,_Tv=_Ts.c,_Tw=E(_Tm.c),_Tx=_Tw.a,_Ty=_Tw.b,_Tz=_Tw.c,_TA=E(_Tm.e);if(_Ta>=_Tp){if(_Ta!=_Tp){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Tb>=_Tq){if(_Tb!=_Tq){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Tc>=_Tr){if(_Tc!=_Tr){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Te>=_Tt){if(_Te!=_Tt){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Tf>=_Tu){if(_Tf!=_Tu){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Tg>=_Tv){if(_Tg!=_Tv){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Ti>=_Tx){if(_Ti!=_Tx){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Tj>=_Ty){if(_Tj!=_Ty){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_Tk>=_Tz){if(_Tk!=_Tz){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{if(_T8>=_Tn){if(_T8!=_Tn){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{var _TB=E(_Tl.a),_TC=E(_TA.a);if(_TB>=_TC){if(_TB!=_TC){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{var _TD=E(_Tl.b),_TE=E(_TA.b);if(_TD>=_TE){if(_TD!=_TE){return new F(function(){return _IV(_SW,_SU,B(_SO(_SX,_SZ,_T7,_SV)));});}else{return new F(function(){return _RH(_SU,_SV);});}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_T7,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_SR,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_SR,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SZ,_SR,_SU)),_SV);});}}}else{return new F(function(){return _Jx(_SW,B(_SO(_SX,_SQ,_SR,_SU)),_SV);});}}else{return new T0(1);}},_TF=function(_TG,_TH){while(1){var _TI=E(_TH);if(!_TI._){var _TJ=E(_TI.b),_TK=B(_SO(_TJ.a,_TJ.b,_TJ.c,B(_TF(_TG,_TI.d))));_TG=_TK;_TH=_TI.c;continue;}else{return E(_TG);}}},_TL=function(_TM,_TN){while(1){var _TO=E(_TN);if(!_TO._){var _TP=E(_TO.b),_TQ=B(_SO(_TP.a,_TP.b,_TP.c,B(_TL(_TM,_TO.d))));_TM=_TQ;_TN=_TO.c;continue;}else{return E(_TM);}}},_TR=function(_TS,_TT,_TU){while(1){var _TV=E(_TU);if(!_TV._){return E(_TT);}else{_TS=_TV.a;_TT=_TV.b;_TU=_TV.c;continue;}}},_TW=new T(function(){return B(unCStr("lookFor: Breakpoint does not exist."));}),_TX=new T(function(){return B(err(_TW));}),_TY=function(_TZ,_U0,_U1,_U2,_U3,_U4,_U5,_U6){var _U7=E(_U6);if(!_U7._){return __Z;}else{var _U8=E(_U7.b),_U9=E(_U8.a),_Ua=_U9.b,_Ub=_U9.c,_Uc=E(_U8.b),_Ud=_Uc.b,_Ue=_Uc.c,_Uf=function(_Ug){var _Uh=_U1-_U4,_Ui=function(_Uj){var _Uk=_Ub-_Ue,_Ul=function(_Um){if(_Uj>=_Um){if(_Uj<_Um){return E(_TX);}else{return new F(function(){return _TY(_TZ,_U0,_U1,_U2,_U3,_U4,_U5,_U7.c);});}}else{return new F(function(){return _TY(_TZ,_U0,_U1,_U2,_U3,_U4,_U5,_U7.a);});}};if(_Uk!=0){if(_Uk<=0){if( -_Uk>=1.0e-7){var _Un=E(_U5);return new F(function(){return _Ul((_Ub*_Ud+Math.sqrt(((_Ua-_Ud)*(_Ua-_Ud)+_Uk*_Uk)*(_Ub-_Un)*(_Ue-_Un))+(_Ua*(_Un-_Ue)-_Ud*_Un))/_Uk);});}else{return new F(function(){return _Ul((_Ua+_Ud)/2);});}}else{if(_Uk>=1.0e-7){var _Uo=E(_U5);return new F(function(){return _Ul((_Ub*_Ud+Math.sqrt(((_Ua-_Ud)*(_Ua-_Ud)+_Uk*_Uk)*(_Ub-_Uo)*(_Ue-_Uo))+(_Ua*(_Uo-_Ue)-_Ud*_Uo))/_Uk);});}else{return new F(function(){return _Ul((_Ua+_Ud)/2);});}}}else{return new F(function(){return _Ul((_Ua+_Ud)/2);});}};if(_Uh!=0){if(_Uh<=0){if( -_Uh>=1.0e-7){var _Up=E(_U5);return new F(function(){return _Ui((_U1*_U3+Math.sqrt(((_U0-_U3)*(_U0-_U3)+_Uh*_Uh)*(_U1-_Up)*(_U4-_Up))+(_U0*(_Up-_U4)-_U3*_Up))/_Uh);});}else{return new F(function(){return _Ui((_U0+_U3)/2);});}}else{if(_Uh>=1.0e-7){var _Uq=E(_U5);return new F(function(){return _Ui((_U1*_U3+Math.sqrt(((_U0-_U3)*(_U0-_U3)+_Uh*_Uh)*(_U1-_Uq)*(_U4-_Uq))+(_U0*(_Uq-_U4)-_U3*_Uq))/_Uh);});}else{return new F(function(){return _Ui((_U0+_U3)/2);});}}}else{return new F(function(){return _Ui((_U0+_U3)/2);});}};if(_U9.a!=_TZ){return new F(function(){return _Uf(_);});}else{if(_Uc.a!=_U2){return new F(function(){return _Uf(_);});}else{return E(_U7);}}}},_Ur=function(_Us,_Ut,_Uu){var _Uv=E(_Uu);if(!_Uv._){return __Z;}else{var _Uw=E(_Uv.b),_Ux=E(_Uw.a),_Uy=_Ux.b,_Uz=_Ux.c,_UA=E(_Uw.b),_UB=_UA.b,_UC=_UA.c,_UD=E(_Us),_UE=E(_UD.a),_UF=_UE.a,_UG=_UE.b,_UH=_UE.c,_UI=E(_UD.b),_UJ=_UI.a,_UK=_UI.b,_UL=_UI.c,_UM=function(_UN){var _UO=_UH-_UL,_UP=function(_UQ){var _UR=_Uz-_UC,_US=function(_UT){if(_UQ>=_UT){if(_UQ<_UT){return E(_TX);}else{return new F(function(){return _TY(_UF,_UG,_UH,_UJ,_UK,_UL,_Ut,_Uv.c);});}}else{return new F(function(){return _TY(_UF,_UG,_UH,_UJ,_UK,_UL,_Ut,_Uv.a);});}};if(_UR!=0){if(_UR<=0){if( -_UR>=1.0e-7){var _UU=E(_Ut);return new F(function(){return _US((_Uz*_UB+Math.sqrt(((_Uy-_UB)*(_Uy-_UB)+_UR*_UR)*(_Uz-_UU)*(_UC-_UU))+(_Uy*(_UU-_UC)-_UB*_UU))/_UR);});}else{return new F(function(){return _US((_Uy+_UB)/2);});}}else{if(_UR>=1.0e-7){var _UV=E(_Ut);return new F(function(){return _US((_Uz*_UB+Math.sqrt(((_Uy-_UB)*(_Uy-_UB)+_UR*_UR)*(_Uz-_UV)*(_UC-_UV))+(_Uy*(_UV-_UC)-_UB*_UV))/_UR);});}else{return new F(function(){return _US((_Uy+_UB)/2);});}}}else{return new F(function(){return _US((_Uy+_UB)/2);});}};if(_UO!=0){if(_UO<=0){if( -_UO>=1.0e-7){var _UW=E(_Ut);return new F(function(){return _UP((_UH*_UK+Math.sqrt(((_UG-_UK)*(_UG-_UK)+_UO*_UO)*(_UH-_UW)*(_UL-_UW))+(_UG*(_UW-_UL)-_UK*_UW))/_UO);});}else{return new F(function(){return _UP((_UG+_UK)/2);});}}else{if(_UO>=1.0e-7){var _UX=E(_Ut);return new F(function(){return _UP((_UH*_UK+Math.sqrt(((_UG-_UK)*(_UG-_UK)+_UO*_UO)*(_UH-_UX)*(_UL-_UX))+(_UG*(_UX-_UL)-_UK*_UX))/_UO);});}else{return new F(function(){return _UP((_UG+_UK)/2);});}}}else{return new F(function(){return _UP((_UG+_UK)/2);});}};if(_Ux.a!=_UF){return new F(function(){return _UM(_);});}else{if(_UA.a!=_UJ){return new F(function(){return _UM(_);});}else{return E(_Uv);}}}},_UY=new T3(0,0,0,0),_UZ=new T2(0,E(_UY),E(_UY)),_V0=function(_V1,_V2,_V3){var _V4=function(_V5){var _V6=E(_V3);if(!_V6._){return E(_UZ);}else{var _V7=E(_V6.b),_V8=E(_V7.a),_V9=_V8.b,_Va=_V8.c,_Vb=E(_V7.b),_Vc=_Vb.b,_Vd=_Vb.c,_Ve=E(_V1),_Vf=E(_Ve.a),_Vg=_Vf.a,_Vh=E(_Ve.b),_Vi=_Vh.a,_Vj=function(_Vk){var _Vl=B(_NH(_Vf.b,_Vf.c,_Vh.b,_Vh.c,_V2)),_Vm=_Va-_Vd,_Vn=function(_Vo){if(_Vl>=_Vo){if(_Vl<=_Vo){return E(_UZ);}else{var _Vp=function(_Vq,_Vr){var _Vs=E(_Vr);if(!_Vs._){return E(_Vq);}else{var _Vt=E(_Vs.b),_Vu=E(_Vt.a),_Vv=_Vu.b,_Vw=_Vu.c,_Vx=E(_Vt.b),_Vy=_Vx.b,_Vz=_Vx.c,_VA=function(_VB){var _VC=_Vw-_Vz,_VD=function(_VE){if(_Vl>=_VE){if(_Vl<=_VE){return E(_Vq);}else{return new F(function(){return _Vp(_Vt,_Vs.c);});}}else{return new F(function(){return _Vp(_Vq,_Vs.a);});}};if(_VC!=0){if(_VC<=0){if( -_VC>=1.0e-7){var _VF=E(_V2);return new F(function(){return _VD((_Vw*_Vy+Math.sqrt(((_Vv-_Vy)*(_Vv-_Vy)+_VC*_VC)*(_Vw-_VF)*(_Vz-_VF))+(_Vv*(_VF-_Vz)-_Vy*_VF))/_VC);});}else{return new F(function(){return _VD((_Vv+_Vy)/2);});}}else{if(_VC>=1.0e-7){var _VG=E(_V2);return new F(function(){return _VD((_Vw*_Vy+Math.sqrt(((_Vv-_Vy)*(_Vv-_Vy)+_VC*_VC)*(_Vw-_VG)*(_Vz-_VG))+(_Vv*(_VG-_Vz)-_Vy*_VG))/_VC);});}else{return new F(function(){return _VD((_Vv+_Vy)/2);});}}}else{return new F(function(){return _VD((_Vv+_Vy)/2);});}};if(_Vu.a!=_Vg){return new F(function(){return _VA(_);});}else{if(_Vx.a!=_Vi){return new F(function(){return _VA(_);});}else{return E(_Vq);}}}};return new F(function(){return _Vp(_V7,_V6.c);});}}else{var _VH=function(_VI,_VJ){var _VK=E(_VJ);if(!_VK._){return E(_VI);}else{var _VL=E(_VK.b),_VM=E(_VL.a),_VN=_VM.b,_VO=_VM.c,_VP=E(_VL.b),_VQ=_VP.b,_VR=_VP.c,_VS=function(_VT){var _VU=_VO-_VR,_VV=function(_VW){if(_Vl>=_VW){if(_Vl<=_VW){return E(_VI);}else{return new F(function(){return _VH(_VL,_VK.c);});}}else{return new F(function(){return _VH(_VI,_VK.a);});}};if(_VU!=0){if(_VU<=0){if( -_VU>=1.0e-7){var _VX=E(_V2);return new F(function(){return _VV((_VO*_VQ+Math.sqrt(((_VN-_VQ)*(_VN-_VQ)+_VU*_VU)*(_VO-_VX)*(_VR-_VX))+(_VN*(_VX-_VR)-_VQ*_VX))/_VU);});}else{return new F(function(){return _VV((_VN+_VQ)/2);});}}else{if(_VU>=1.0e-7){var _VY=E(_V2);return new F(function(){return _VV((_VO*_VQ+Math.sqrt(((_VN-_VQ)*(_VN-_VQ)+_VU*_VU)*(_VO-_VY)*(_VR-_VY))+(_VN*(_VY-_VR)-_VQ*_VY))/_VU);});}else{return new F(function(){return _VV((_VN+_VQ)/2);});}}}else{return new F(function(){return _VV((_VN+_VQ)/2);});}};if(_VM.a!=_Vg){return new F(function(){return _VS(_);});}else{if(_VP.a!=_Vi){return new F(function(){return _VS(_);});}else{return E(_VI);}}}};return new F(function(){return _VH(_UZ,_V6.a);});}};if(_Vm!=0){if(_Vm<=0){if( -_Vm>=1.0e-7){var _VZ=E(_V2);return new F(function(){return _Vn((_Va*_Vc+Math.sqrt(((_V9-_Vc)*(_V9-_Vc)+_Vm*_Vm)*(_Va-_VZ)*(_Vd-_VZ))+(_V9*(_VZ-_Vd)-_Vc*_VZ))/_Vm);});}else{return new F(function(){return _Vn((_V9+_Vc)/2);});}}else{if(_Vm>=1.0e-7){var _W0=E(_V2);return new F(function(){return _Vn((_Va*_Vc+Math.sqrt(((_V9-_Vc)*(_V9-_Vc)+_Vm*_Vm)*(_Va-_W0)*(_Vd-_W0))+(_V9*(_W0-_Vd)-_Vc*_W0))/_Vm);});}else{return new F(function(){return _Vn((_V9+_Vc)/2);});}}}else{return new F(function(){return _Vn((_V9+_Vc)/2);});}};if(_V8.a!=_Vg){return new F(function(){return _Vj(_);});}else{if(_Vb.a!=_Vi){return new F(function(){return _Vj(_);});}else{return E(_UZ);}}}},_W1=B(_Ur(_V1,_V2,_V3));if(!_W1._){return new F(function(){return _V4(_);});}else{var _W2=E(_W1.a);if(!_W2._){return new F(function(){return _V4(_);});}else{return new F(function(){return _TR(_W2.a,_W2.b,_W2.c);});}}},_W3=function(_W4,_W5,_W6){var _W7=function(_W8){var _W9=E(_W6);if(!_W9._){return E(_UZ);}else{var _Wa=E(_W9.b),_Wb=E(_Wa.a),_Wc=_Wb.b,_Wd=_Wb.c,_We=E(_Wa.b),_Wf=_We.b,_Wg=_We.c,_Wh=E(_W4),_Wi=E(_Wh.a),_Wj=_Wi.a,_Wk=E(_Wh.b),_Wl=_Wk.a,_Wm=function(_Wn){var _Wo=B(_NH(_Wi.b,_Wi.c,_Wk.b,_Wk.c,_W5)),_Wp=_Wd-_Wg,_Wq=function(_Wr){if(_Wo>=_Wr){if(_Wo<=_Wr){return E(_UZ);}else{var _Ws=function(_Wt,_Wu){var _Wv=E(_Wu);if(!_Wv._){return E(_Wt);}else{var _Ww=E(_Wv.b),_Wx=E(_Ww.a),_Wy=_Wx.b,_Wz=_Wx.c,_WA=E(_Ww.b),_WB=_WA.b,_WC=_WA.c,_WD=function(_WE){var _WF=_Wz-_WC,_WG=function(_WH){if(_Wo>=_WH){if(_Wo<=_WH){return E(_Wt);}else{return new F(function(){return _Ws(_Wt,_Wv.c);});}}else{return new F(function(){return _Ws(_Ww,_Wv.a);});}};if(_WF!=0){if(_WF<=0){if( -_WF>=1.0e-7){var _WI=E(_W5);return new F(function(){return _WG((_Wz*_WB+Math.sqrt(((_Wy-_WB)*(_Wy-_WB)+_WF*_WF)*(_Wz-_WI)*(_WC-_WI))+(_Wy*(_WI-_WC)-_WB*_WI))/_WF);});}else{return new F(function(){return _WG((_Wy+_WB)/2);});}}else{if(_WF>=1.0e-7){var _WJ=E(_W5);return new F(function(){return _WG((_Wz*_WB+Math.sqrt(((_Wy-_WB)*(_Wy-_WB)+_WF*_WF)*(_Wz-_WJ)*(_WC-_WJ))+(_Wy*(_WJ-_WC)-_WB*_WJ))/_WF);});}else{return new F(function(){return _WG((_Wy+_WB)/2);});}}}else{return new F(function(){return _WG((_Wy+_WB)/2);});}};if(_Wx.a!=_Wj){return new F(function(){return _WD(_);});}else{if(_WA.a!=_Wl){return new F(function(){return _WD(_);});}else{return E(_Wt);}}}};return new F(function(){return _Ws(_UZ,_W9.c);});}}else{var _WK=function(_WL,_WM){var _WN=E(_WM);if(!_WN._){return E(_WL);}else{var _WO=E(_WN.b),_WP=E(_WO.a),_WQ=_WP.b,_WR=_WP.c,_WS=E(_WO.b),_WT=_WS.b,_WU=_WS.c,_WV=function(_WW){var _WX=_WR-_WU,_WY=function(_WZ){if(_Wo>=_WZ){if(_Wo<=_WZ){return E(_WL);}else{return new F(function(){return _WK(_WL,_WN.c);});}}else{return new F(function(){return _WK(_WO,_WN.a);});}};if(_WX!=0){if(_WX<=0){if( -_WX>=1.0e-7){var _X0=E(_W5);return new F(function(){return _WY((_WR*_WT+Math.sqrt(((_WQ-_WT)*(_WQ-_WT)+_WX*_WX)*(_WR-_X0)*(_WU-_X0))+(_WQ*(_X0-_WU)-_WT*_X0))/_WX);});}else{return new F(function(){return _WY((_WQ+_WT)/2);});}}else{if(_WX>=1.0e-7){var _X1=E(_W5);return new F(function(){return _WY((_WR*_WT+Math.sqrt(((_WQ-_WT)*(_WQ-_WT)+_WX*_WX)*(_WR-_X1)*(_WU-_X1))+(_WQ*(_X1-_WU)-_WT*_X1))/_WX);});}else{return new F(function(){return _WY((_WQ+_WT)/2);});}}}else{return new F(function(){return _WY((_WQ+_WT)/2);});}};if(_WP.a!=_Wj){return new F(function(){return _WV(_);});}else{if(_WS.a!=_Wl){return new F(function(){return _WV(_);});}else{return E(_WL);}}}};return new F(function(){return _WK(_Wa,_W9.a);});}};if(_Wp!=0){if(_Wp<=0){if( -_Wp>=1.0e-7){var _X2=E(_W5);return new F(function(){return _Wq((_Wd*_Wf+Math.sqrt(((_Wc-_Wf)*(_Wc-_Wf)+_Wp*_Wp)*(_Wd-_X2)*(_Wg-_X2))+(_Wc*(_X2-_Wg)-_Wf*_X2))/_Wp);});}else{return new F(function(){return _Wq((_Wc+_Wf)/2);});}}else{if(_Wp>=1.0e-7){var _X3=E(_W5);return new F(function(){return _Wq((_Wd*_Wf+Math.sqrt(((_Wc-_Wf)*(_Wc-_Wf)+_Wp*_Wp)*(_Wd-_X3)*(_Wg-_X3))+(_Wc*(_X3-_Wg)-_Wf*_X3))/_Wp);});}else{return new F(function(){return _Wq((_Wc+_Wf)/2);});}}}else{return new F(function(){return _Wq((_Wc+_Wf)/2);});}};if(_Wb.a!=_Wj){return new F(function(){return _Wm(_);});}else{if(_We.a!=_Wl){return new F(function(){return _Wm(_);});}else{return E(_UZ);}}}},_X4=B(_Ur(_W4,_W5,_W6));if(!_X4._){return new F(function(){return _W7(_);});}else{var _X5=E(_X4.c);if(!_X5._){return new F(function(){return _W7(_);});}else{return new F(function(){return _LL(_X5.a,_X5.b,_X5.c);});}}},_X6=function(_X7,_X8,_X9,_Xa){var _Xb=E(_Xa);if(!_Xb._){return new T3(1,_OS,_X8,_OS);}else{var _Xc=_Xb.a,_Xd=_Xb.c,_Xe=E(_Xb.b),_Xf=E(_Xe.a),_Xg=_Xf.b,_Xh=_Xf.c,_Xi=E(_Xe.b),_Xj=_Xi.b,_Xk=_Xi.c,_Xl=_Xh-_Xk,_Xm=function(_Xn){return (_X7>=_Xn)?new T3(1,_Xc,_Xe,new T(function(){return B(_X6(_X7,_X8,_X9,_Xd));})):new T3(1,new T(function(){return B(_X6(_X7,_X8,_X9,_Xc));}),_Xe,_Xd);};if(_Xl!=0){if(_Xl<=0){if( -_Xl>=1.0e-7){var _Xo=E(_X9);return new F(function(){return _Xm((_Xh*_Xj+Math.sqrt(((_Xg-_Xj)*(_Xg-_Xj)+_Xl*_Xl)*(_Xh-_Xo)*(_Xk-_Xo))+(_Xg*(_Xo-_Xk)-_Xj*_Xo))/_Xl);});}else{return new F(function(){return _Xm((_Xg+_Xj)/2);});}}else{if(_Xl>=1.0e-7){var _Xp=E(_X9);return new F(function(){return _Xm((_Xh*_Xj+Math.sqrt(((_Xg-_Xj)*(_Xg-_Xj)+_Xl*_Xl)*(_Xh-_Xp)*(_Xk-_Xp))+(_Xg*(_Xp-_Xk)-_Xj*_Xp))/_Xl);});}else{return new F(function(){return _Xm((_Xg+_Xj)/2);});}}}else{return new F(function(){return _Xm((_Xg+_Xj)/2);});}}},_Xq=function(_Xr,_Xs,_Xt,_Xu){var _Xv=E(_Xu);if(!_Xv._){return new T3(1,_OS,_Xs,_OS);}else{var _Xw=_Xv.a,_Xx=_Xv.c,_Xy=E(_Xr),_Xz=E(_Xv.b),_XA=E(_Xz.a),_XB=_XA.b,_XC=_XA.c,_XD=E(_Xz.b),_XE=_XD.b,_XF=_XD.c,_XG=_XC-_XF,_XH=function(_XI){return (_Xy>=_XI)?new T3(1,_Xw,_Xz,new T(function(){return B(_X6(_Xy,_Xs,_Xt,_Xx));})):new T3(1,new T(function(){return B(_X6(_Xy,_Xs,_Xt,_Xw));}),_Xz,_Xx);};if(_XG!=0){if(_XG<=0){if( -_XG>=1.0e-7){var _XJ=E(_Xt);return new F(function(){return _XH((_XC*_XE+Math.sqrt(((_XB-_XE)*(_XB-_XE)+_XG*_XG)*(_XC-_XJ)*(_XF-_XJ))+(_XB*(_XJ-_XF)-_XE*_XJ))/_XG);});}else{return new F(function(){return _XH((_XB+_XE)/2);});}}else{if(_XG>=1.0e-7){var _XK=E(_Xt);return new F(function(){return _XH((_XC*_XE+Math.sqrt(((_XB-_XE)*(_XB-_XE)+_XG*_XG)*(_XC-_XK)*(_XF-_XK))+(_XB*(_XK-_XF)-_XE*_XK))/_XG);});}else{return new F(function(){return _XH((_XB+_XE)/2);});}}}else{return new F(function(){return _XH((_XB+_XE)/2);});}}},_XL=0,_XM=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_XN=function(_XO){return new F(function(){return _7G(new T1(0,new T(function(){return B(_7T(_XO,_XM));})),_7q);});},_XP=new T(function(){return B(_XN("Fortune/Fortune.hs:(311,19)-(314,56)|multi-way if"));}),_XQ=function(_XR,_XS){var _XT=E(_XR);return new F(function(){return _K7(_ID,new T3(0,_XT.d,new T3(0,E(_XT.a).a,E(_XT.b).a,E(_XT.c).a),_XT),_XS);});},_XU=new T(function(){return B(_84("Fortune/Fortune.hs:(117,1)-(118,32)|function setVert"));}),_XV=function(_XW,_XX){var _XY=E(E(_XW).a),_XZ=E(E(_XX).a);return (_XY>=_XZ)?(_XY!=_XZ)?2:1:0;},_Y0=function(_Y1){var _Y2=E(_Y1),_Y3=E(_Y2.b);return new T2(0,_Y3,_Y2);},_Y4=0,_Y5=new T3(0,_Y4,_Y4,_Y4),_Y6=function(_Y7,_Y8){if(_Y7<=_Y8){var _Y9=function(_Ya){return new T2(1,_Ya,new T(function(){if(_Ya!=_Y8){return B(_Y9(_Ya+1|0));}else{return __Z;}}));};return new F(function(){return _Y9(_Y7);});}else{return __Z;}},_Yb=new T(function(){return B(_Y6(0,2147483647));}),_Yc=function(_Yd,_Ye){var _Yf=E(_Ye);return (_Yf._==0)?__Z:new T2(1,new T(function(){return B(A1(_Yd,_Yf.a));}),new T(function(){return B(_Yc(_Yd,_Yf.b));}));},_Yg=new T(function(){return B(unCStr("tail"));}),_Yh=new T(function(){return B(_f4(_Yg));}),_Yi=function(_Yj){return E(E(_Yj).b);},_Yk=new T2(1,_6,_6),_Yl=function(_Ym,_Yn){var _Yo=function(_Yp,_Yq){var _Yr=E(_Yp);if(!_Yr._){return E(_Yq);}else{var _Ys=_Yr.a,_Yt=E(_Yq);if(!_Yt._){return E(_Yr);}else{var _Yu=_Yt.a;return (B(A2(_Ym,_Ys,_Yu))==2)?new T2(1,_Yu,new T(function(){return B(_Yo(_Yr,_Yt.b));})):new T2(1,_Ys,new T(function(){return B(_Yo(_Yr.b,_Yt));}));}}},_Yv=function(_Yw){var _Yx=E(_Yw);if(!_Yx._){return __Z;}else{var _Yy=E(_Yx.b);return (_Yy._==0)?E(_Yx):new T2(1,new T(function(){return B(_Yo(_Yx.a,_Yy.a));}),new T(function(){return B(_Yv(_Yy.b));}));}},_Yz=new T(function(){return B(_YA(B(_Yv(_6))));}),_YA=function(_YB){while(1){var _YC=E(_YB);if(!_YC._){return E(_Yz);}else{if(!E(_YC.b)._){return E(_YC.a);}else{_YB=B(_Yv(_YC));continue;}}}},_YD=new T(function(){return B(_YE(_6));}),_YF=function(_YG,_YH,_YI){while(1){var _YJ=B((function(_YK,_YL,_YM){var _YN=E(_YM);if(!_YN._){return new T2(1,new T2(1,_YK,_YL),_YD);}else{var _YO=_YN.a;if(B(A2(_Ym,_YK,_YO))==2){var _YP=new T2(1,_YK,_YL);_YG=_YO;_YH=_YP;_YI=_YN.b;return __continue;}else{return new T2(1,new T2(1,_YK,_YL),new T(function(){return B(_YE(_YN));}));}}})(_YG,_YH,_YI));if(_YJ!=__continue){return _YJ;}}},_YQ=function(_YR,_YS,_YT){while(1){var _YU=B((function(_YV,_YW,_YX){var _YY=E(_YX);if(!_YY._){return new T2(1,new T(function(){return B(A1(_YW,new T2(1,_YV,_6)));}),_YD);}else{var _YZ=_YY.a,_Z0=_YY.b;switch(B(A2(_Ym,_YV,_YZ))){case 0:_YR=_YZ;_YS=function(_Z1){return new F(function(){return A1(_YW,new T2(1,_YV,_Z1));});};_YT=_Z0;return __continue;case 1:_YR=_YZ;_YS=function(_Z2){return new F(function(){return A1(_YW,new T2(1,_YV,_Z2));});};_YT=_Z0;return __continue;default:return new T2(1,new T(function(){return B(A1(_YW,new T2(1,_YV,_6)));}),new T(function(){return B(_YE(_YY));}));}}})(_YR,_YS,_YT));if(_YU!=__continue){return _YU;}}},_YE=function(_Z3){var _Z4=E(_Z3);if(!_Z4._){return E(_Yk);}else{var _Z5=_Z4.a,_Z6=E(_Z4.b);if(!_Z6._){return new T2(1,_Z4,_6);}else{var _Z7=_Z6.a,_Z8=_Z6.b;if(B(A2(_Ym,_Z5,_Z7))==2){return new F(function(){return _YF(_Z7,new T2(1,_Z5,_6),_Z8);});}else{return new F(function(){return _YQ(_Z7,function(_Z9){return new T2(1,_Z5,_Z9);},_Z8);});}}}};return new F(function(){return _YA(B(_YE(_Yn)));});},_Za=function(_Zb,_Zc,_Zd){var _Ze=function(_Zf,_Zg){while(1){var _Zh=B((function(_Zi,_Zj){var _Zk=E(_Zj);if(!_Zk._){var _Zl=_Zk.e,_Zm=E(_Zk.b),_Zn=_Zm.a,_Zo=_Zm.b,_Zp=new T(function(){var _Zq=E(_Zk.c);switch(_Zq._){case 0:return B(_Ze(_Zi,_Zl));break;case 1:var _Zr=E(_Zq.a),_Zs=E(_Zr.a);if(_Zs<0){return B(_Ze(_Zi,_Zl));}else{var _Zt=E(_Zc);if(_Zs>_Zt){return B(_Ze(_Zi,_Zl));}else{var _Zu=E(_Zr.b);if(_Zu<0){return B(_Ze(_Zi,_Zl));}else{var _Zv=E(_Zd);if(_Zu>_Zv){return B(_Ze(_Zi,_Zl));}else{var _Zw=B(_oZ(_Zb,E(_Zn))),_Zx=E(_Zw.a),_Zy=E(_Zw.b),_Zz=B(_oZ(_Zb,E(_Zo))),_ZA=E(_Zz.a),_ZB=E(_Zz.b),_ZC=Math.pow(_Zs-_Zx,2)+Math.pow(_Zu-_Zy,2)-(Math.pow(_Zs-_ZA,2)+Math.pow(_Zu-_ZB,2)),_ZD=function(_ZE,_ZF){var _ZG=E(_ZF);if(_ZG._==2){return new T2(1,new T(function(){var _ZH=E(_ZE);return new T4(0,E(_ZH.a),E(_ZH.b),E(_ZG.a),E(_ZG.b));}),new T(function(){return B(_Ze(_Zi,_Zl));}));}else{return new F(function(){return _Ze(_Zi,_Zl);});}},_ZI=function(_ZJ){if(_ZJ>=1.0e-2){return new T2(0,_Zm,_Zq);}else{var _ZK=new T(function(){var _ZL=_ZA-_Zx,_ZM=(Math.pow(_ZA,2)-Math.pow(_Zx,2)+Math.pow(_ZB,2)-Math.pow(_Zy,2))/2,_ZN=_ZB-_Zy,_ZO=function(_ZP,_ZQ){var _ZR=B(_Q2(2,B(_Yl(function(_ZS,_ZT){var _ZU=E(_ZS),_ZV=E(_ZQ),_ZW=E(_ZT),_ZX=Math.pow(_ZP-E(_ZU.a),2)+Math.pow(_ZV-E(_ZU.b),2),_ZY=Math.pow(_ZP-E(_ZW.a),2)+Math.pow(_ZV-E(_ZW.b),2);return (_ZX>=_ZY)?(_ZX!=_ZY)?2:1:0;},_Zb))));if(!B(_Qo(_B1,_Zw,_ZR))){return false;}else{return new F(function(){return _Qo(_B1,_Zz,_ZR);});}},_ZZ=function(_100,_101){var _102=B(_Q2(2,B(_Yl(function(_103,_104){var _105=E(_103),_106=E(_100),_107=E(_104),_108=Math.pow(_106-E(_105.a),2)+Math.pow(_101-E(_105.b),2),_109=Math.pow(_106-E(_107.a),2)+Math.pow(_101-E(_107.b),2);return (_108>=_109)?(_108!=_109)?2:1:0;},_Zb))));if(!B(_Qo(_B1,_Zw,_102))){return false;}else{return new F(function(){return _Qo(_B1,_Zz,_102);});}},_10a=function(_10b){if(_ZB!=_Zy){var _10c=new T(function(){return (_ZM-_ZL*0)/_ZN;}),_10d=new T(function(){var _10e=new T(function(){return (_ZM-_ZL*_Zt)/_ZN;});if(!B(_ZO(0,_10e))){return __Z;}else{return new T2(1,new T2(0,_XL,_10e),_6);}});return (!B(_ZO(0,_10c)))?E(_10d):new T2(1,new T2(0,_XL,_10c),_10d);}else{if(_ZA!=_Zx){var _10f=new T(function(){return (_ZM-_ZN*0)/_ZL;}),_10g=new T(function(){var _10h=new T(function(){return (_ZM-_ZN*_Zv)/_ZL;});if(!B(_ZZ(_10h,_Zv))){return __Z;}else{return new T2(1,new T2(0,_10h,_Zv),_6);}});return (!B(_ZZ(_10f,0)))?E(_10g):new T2(1,new T2(0,_10f,_XL),_10g);}else{return E(_XP);}}},_10i=function(_10j,_10k){var _10l=E(_10j),_10m=E(_10k),_10n=Math.pow(_Zs-E(_10l.a),2)+Math.pow(_Zu-E(_10l.b),2),_10o=Math.pow(_Zs-E(_10m.a),2)+Math.pow(_Zu-E(_10m.b),2);return (_10n>=_10o)?(_10n!=_10o)?E(_10m):E(_10l):E(_10l);};if(_ZB!=_Zy){if(_ZA!=_Zx){var _10p=new T(function(){return (_ZM-_ZL*0)/_ZN;}),_10q=new T(function(){var _10r=new T(function(){return (_ZM-_ZL*_Zt)/_ZN;}),_10s=new T(function(){var _10t=new T(function(){return (_ZM-_ZN*0)/_ZL;}),_10u=new T(function(){var _10v=new T(function(){return (_ZM-_ZN*_Zv)/_ZL;});if(!B(_ZZ(_10v,_Zv))){return __Z;}else{return new T2(1,new T2(0,_10v,_Zv),_6);}});if(!B(_ZZ(_10t,0))){return E(_10u);}else{return new T2(1,new T2(0,_10t,_XL),_10u);}});if(!B(_ZO(0,_10r))){return E(_10s);}else{return new T2(1,new T2(0,_XL,_10r),_10s);}});if(!B(_ZO(0,_10p))){var _10w=B(_f8(_10i,_10q));}else{var _10w=B(_f8(_10i,new T2(1,new T2(0,_XL,_10p),_10q)));}var _10x=_10w;}else{var _10x=B(_f8(_10i,B(_10a(_))));}var _10y=_10x;}else{var _10y=B(_f8(_10i,B(_10a(_))));}return new T2(2,E(_Zr),E(_10y));});return new T2(0,_Zm,_ZK);}};if(_ZC!=0){if(_ZC<=0){var _10z=B(_ZI( -_ZC));return B(_ZD(_10z.a,_10z.b));}else{var _10A=B(_ZI(_ZC));return B(_ZD(_10A.a,_10A.b));}}else{var _10B=B(_ZI(0));return B(_ZD(_10B.a,_10B.b));}}}}}break;default:return new T2(1,new T(function(){return new T4(0,E(_Zn),E(_Zo),E(_Zq.a),E(_Zq.b));}),new T(function(){return B(_Ze(_Zi,_Zl));}));}},1);_Zf=_Zp;_Zg=_Zk.d;return __continue;}else{return E(_Zi);}})(_Zf,_Zg));if(_Zh!=__continue){return _Zh;}}},_10C=function(_10D,_10E,_10F){var _10G=new T(function(){var _10H=E(_10D),_10I=_10H.b,_10J=_10H.c,_10K=_10H.d,_10L=E(_10H.a),_10M=_10L.a,_10N=_10L.b,_10O=new T(function(){var _10P=new T(function(){var _10Q=function(_10R){var _10S=new T(function(){var _10T=E(_10N);if(!_10T._){var _10U=E(_10T.c);if(!_10U._){return B(_Sy(_10U.a,_10U.b,_10U.c,_10U.d));}else{return E(_10T.b);}}else{return E(_Sx);}}),_10V=function(_10W){var _10X=new T(function(){var _10Y=E(_10K);return new T5(0,1,E(_10Y),new T4(0,_cm,_10J,_10I,new T(function(){return E(E(_10S).b);})),E(_wv),E(_wv));}),_10Z=new T(function(){var _110=E(_10N);if(!_110._){var _111=E(_110.c);if(!_111._){var _112=E(B(_Sy(_111.a,_111.b,_111.c,_111.d)).c),_113=E(_112.a),_114=E(_112.b),_115=E(_112.c);return {_:0,a:_113,b:_113.a,c:_114,d:_114.a,e:_115,f:_115.a,g:_112.d,h:_112.e};}else{var _116=E(E(_110.b).c),_117=E(_116.a),_118=E(_116.b),_119=E(_116.c);return {_:0,a:_117,b:_117.a,c:_118,d:_118.a,e:_119,f:_119.a,g:_116.d,h:_116.e};}}else{return E(_Sx);}}),_11a=new T(function(){return E(E(_10Z).h);}),_11b=new T(function(){return E(E(_10Z).a);}),_11c=new T(function(){return E(E(_10Z).c);}),_11d=new T(function(){return new T2(0,E(_11b),E(_11c));}),_11e=new T(function(){return E(E(_10Z).g);}),_11f=new T(function(){return (E(_11e)+E(_10K))/2;}),_11g=new T(function(){return E(E(_10Z).e);}),_11h=new T(function(){return new T2(0,E(_11c),E(_11g));}),_11i=new T(function(){var _11j=E(_11b).a,_11k=E(_11g).a,_11l=E(_11c).a,_11m=function(_11n,_11o){var _11p=function(_11q,_11r){var _11s=new T(function(){return new T1(1,E(_11a));}),_11t=function(_11u,_11v){return new T1(1,new T(function(){var _11w=E(_11v);switch(_11w._){case 0:return E(_11s);break;case 1:return new T2(2,E(_11w.a),E(_11a));break;default:return E(_XU);}}));},_11x=function(_11y,_11z){return new T1(1,new T(function(){var _11A=E(_11z);switch(_11A._){case 0:return E(_11s);break;case 1:return new T2(2,E(_11A.a),E(_11a));break;default:return E(_XU);}}));},_11B=B(_La(_11x,_11n,_11o,B(_La(_11t,_11q,_11r,_10J))));if(_11j>=_11k){return new F(function(){return _IE(_11k,_11j,_11s,_11B);});}else{return new F(function(){return _IE(_11j,_11k,_11s,_11B);});}};if(_11l>=_11k){return new F(function(){return _11p(_11k,_11l);});}else{return new F(function(){return _11p(_11l,_11k);});}};if(_11j>=_11l){return B(_11m(_11l,_11j));}else{return B(_11m(_11j,_11l));}}),_11C=new T(function(){var _11D=E(_11d),_11E=E(_11D.a),_11F=E(_11D.b),_11G=E(_11h),_11H=E(_11G.a),_11I=E(_11G.b);return B(_Xq(new T(function(){return E(E(_11a).a);},1),new T2(0,E(_11E),E(_11I)),_11e,B(_NS(_11E.a,_11E.b,_11E.c,_11F.a,_11F.b,_11F.c,_11H.a,_11H.b,_11H.c,_11I.a,_11I.b,_11I.c,_11f,_10I))));}),_11J=new T(function(){var _11K=B(_V0(_11d,_11f,_10I)),_11L=E(_11K.a),_11M=_11L.a,_11N=_11L.b,_11O=_11L.c,_11P=E(_11K.b).a,_11Q=B(_W3(_11h,_11f,_10I)),_11R=E(_11Q.a).a,_11S=E(_11Q.b),_11T=_11S.a,_11U=_11S.b,_11V=_11S.c,_11W=new T(function(){var _11X=new T(function(){return E(E(_10Z).f);}),_11Y=new T(function(){return E(E(_10Z).d);}),_11Z=new T(function(){return E(E(_10Z).b);}),_120=function(_121){return (E(_11R)==0)?(E(_11T)==0)?new T2(1,new T3(0,_11Z,_11Y,_11X),new T2(1,new T3(0,_11M,_11Z,_11Y),_6)):new T2(1,new T3(0,_11Z,_11Y,_11X),new T2(1,new T3(0,_11M,_11Z,_11Y),new T2(1,new T3(0,_11Y,_11X,_11T),_6))):new T2(1,new T3(0,_11Z,_11Y,_11X),new T2(1,new T3(0,_11M,_11Z,_11Y),new T2(1,new T3(0,_11Y,_11X,_11T),_6)));};if(!E(_11M)){if(!E(_11P)){return new T2(1,new T3(0,_11Z,_11Y,_11X),new T2(1,new T3(0,_11Y,_11X,_11T),_6));}else{return B(_120(_));}}else{return B(_120(_));}}),_122=function(_123){return new F(function(){return _Qo(_wr,new T(function(){return E(E(_123).b);}),_11W);});},_124=B(_TL(_10N,B(_Sp(_122,_10N)))),_125=function(_126){var _127=function(_128){var _129=function(_12a){var _12b=E(_12a);if(!_12b._){return E(_124);}else{var _12c=E(_12b.a);return new F(function(){return _K7(_ID,new T3(0,_12c.d,new T3(0,E(_12c.a).a,E(_12c.b).a,E(_12c.c).a),_12c),B(_129(_12b.b)));});}};return new F(function(){return _129(B(_Q9(new T2(1,new T(function(){var _12d=E(_11b),_12e=E(_11g);return B(_Lp(_Zd,_12d.a,_12d.b,_12d.c,_12e.a,_12e.b,_12e.c,_11T,_11U,_11V));}),new T2(1,new T(function(){var _12f=E(_11b),_12g=E(_11g);return B(_Lp(_Zd,_11M,_11N,_11O,_12f.a,_12f.b,_12f.c,_12g.a,_12g.b,_12g.c));}),_6)))));});};if(!E(_11R)){if(!E(_11T)){var _12h=E(_11b),_12i=E(_11g),_12j=B(_Lp(_Zd,_11M,_11N,_11O,_12h.a,_12h.b,_12h.c,_12i.a,_12i.b,_12i.c));if(!_12j._){return E(_124);}else{return new F(function(){return _XQ(_12j.a,_124);});}}else{return new F(function(){return _127(_);});}}else{return new F(function(){return _127(_);});}};if(!E(_11M)){if(!E(_11P)){var _12k=E(_11b),_12l=E(_11g),_12m=B(_Lp(_Zd,_12k.a,_12k.b,_12k.c,_12l.a,_12l.b,_12l.c,_11T,_11U,_11V));if(!_12m._){return E(_124);}else{return B(_XQ(_12m.a,_124));}}else{return B(_125(_));}}else{return B(_125(_));}});return new T2(0,new T4(0,new T2(0,_10M,_11J),_11C,_11i,_11e),_10X);},_12n=E(_10M);if(!_12n._){return new F(function(){return _10V(_);});}else{var _12o=_12n.a,_12p=function(_12q){var _12r=new T(function(){var _12s=E(_12o);return new T3(0,_12s,_12s.a,_12s.c);}),_12t=new T(function(){return E(E(_12r).c);}),_12u=new T(function(){return E(E(_12r).a);}),_12v=new T(function(){var _12w=E(_12u),_12x=B(_OV(_12w.a,_12w.b,_12w.c,_12t,_10I));return new T2(0,_12x.a,_12x.b);}),_12y=new T(function(){return E(E(_12v).b);}),_12z=new T(function(){var _12A=E(_12y);if(!_12A._){return E(E(_12A.a).a);}else{return E(E(_12A.a).b);}}),_12B=new T(function(){var _12C=function(_12D,_12E){var _12F=E(_12D),_12G=E(_12F.a);if(!E(_12G.a)){if(!E(E(_12F.b).a)){var _12H=__Z;}else{var _12H=new T1(1,new T3(0,0,_12G.b,_12G.c));}var _12I=_12H;}else{var _12I=new T1(1,_12G);}var _12J=new T(function(){var _12K=E(_12E),_12L=E(_12K.b);if(!E(E(_12K.a).a)){if(!E(_12L.a)){return __Z;}else{return new T1(1,_12L);}}else{return new T1(1,_12L);}}),_12M=E(_12I);if(!_12M._){var _12N=E(_10N);}else{var _12O=E(_12J);if(!_12O._){var _12P=E(_10N);}else{var _12Q=new T(function(){return E(_12O.a).a;}),_12P=B(_TF(_10N,B(_Sp(function(_12R){var _12S=E(E(_12R).b);if(E(_12S.a)!=E(_12M.a).a){return false;}else{if(E(_12S.b)!=E(_12z).a){return false;}else{return new F(function(){return _wc(_12S.c,_12Q);});}}},_10N))));}var _12N=_12P;}var _12T=function(_12U){var _12V=E(_12U);if(!_12V._){return E(_12N);}else{var _12W=E(_12V.a);return new F(function(){return _K7(_ID,new T3(0,_12W.d,new T3(0,E(_12W.a).a,E(_12W.b).a,E(_12W.c).a),_12W),B(_12T(_12V.b)));});}};return new F(function(){return _12T(B(_Q9(new T2(1,new T(function(){var _12X=E(_12I);if(!_12X._){return __Z;}else{return B(_Qg(_Zd,_12X.a,_12z,_12u));}}),new T2(1,new T(function(){var _12Y=E(_12J);if(!_12Y._){return __Z;}else{return B(_Qg(_Zd,_12u,_12z,_12Y.a));}}),_6)))));});},_12Z=E(_12y);if(!_12Z._){var _130=_12Z.a;return B(_12C(new T(function(){return B(_V0(_130,_12t,_10I));}),_130));}else{var _131=_12Z.a;return B(_12C(_131,new T(function(){return B(_W3(_131,_12t,_10I));})));}});return new T2(0,new T4(0,new T2(0,_12n.b,_12B),new T(function(){return E(E(_12v).a);}),new T(function(){var _132=E(E(_12r).b),_133=E(_12z).a;if(_132>=_133){return B(_IE(_133,_132,_Q8,_10J));}else{return B(_IE(_132,_133,_Q8,_10J));}}),_12t),new T(function(){var _134=E(_10K);return new T5(0,1,E(_134),new T4(0,_5i,_10J,_10I,_Y5),E(_wv),E(_wv));}));};if(!E(_10N)._){if(E(E(_10S).a)>E(_12o).c){return new F(function(){return _12p(_);});}else{return new F(function(){return _10V(_);});}}else{return new F(function(){return _12p(_);});}}};if(!E(_10M)._){if(!E(_10N)._){var _135=B(_10Q(_));return new T2(0,_135.a,_135.b);}else{return new T2(0,_10H,_wv);}}else{var _136=B(_10Q(_));return new T2(0,_136.a,_136.b);}}),_137=B(_10C(new T(function(){return E(E(_10P).a);}),new T(function(){return B(_AC(_10E,E(_10P).b));}),_));return new T2(0,_137.a,_137.b);});if(!E(_10M)._){if(!E(_10N)._){return E(_10O);}else{return new T2(0,new T(function(){return B(_Ze(_6,_10J));}),_wv);}}else{return E(_10O);}});return new T2(0,new T(function(){return E(E(_10G).a);}),new T(function(){return B(_AC(_10E,E(_10G).b));}));},_138=new T(function(){return B(_SI(_Yb,new T(function(){return B(_Yc(_Yi,B(_Yl(_XV,B(_Yc(_Y0,_Zb))))));},1)));}),_139=new T(function(){var _13a=B(_oZ(_138,0));return new T2(0,_13a,_13a.a);}),_13b=new T(function(){var _13c=B(_oZ(_138,1));return new T3(0,_13c,_13c.a,_13c.c);}),_13d=new T(function(){return E(E(_139).a);}),_13e=new T(function(){return E(E(_13b).a);}),_13f=new T3(1,_OS,new T(function(){return new T2(0,E(_13d),E(_13e));}),new T3(1,_OS,new T(function(){return new T2(0,E(_13e),E(_13d));}),_OS)),_13g=new T(function(){var _13h=E(E(_139).b),_13i=E(E(_13b).b);if(_13h>=_13i){return new T5(0,1,E(new T2(0,_13i,_13h)),_Q8,E(_wv),E(_wv));}else{return new T5(0,1,E(new T2(0,_13h,_13i)),_Q8,E(_wv),E(_wv));}}),_13j=new T(function(){var _13k=E(_138);if(!_13k._){return E(_Yh);}else{var _13l=E(_13k.b);if(!_13l._){return E(_Yh);}else{var _13m=E(_13l.b);if(!_13m._){return new T2(0,new T(function(){return B(_Ze(_6,_13g));}),_wv);}else{var _13n=new T(function(){var _13o=E(_13m.a);return new T3(0,_13o,_13o.a,_13o.c);}),_13p=new T(function(){return E(E(_13n).c);}),_13q=new T(function(){return E(E(_13n).a);}),_13r=new T(function(){var _13s=E(_13q),_13t=B(_OV(_13s.a,_13s.b,_13s.c,_13p,_13f));return new T2(0,_13t.a,_13t.b);}),_13u=new T(function(){return E(E(_13r).b);}),_13v=new T(function(){var _13w=E(_13u);if(!_13w._){return E(E(_13w.a).a);}else{return E(E(_13w.a).b);}}),_13x=new T(function(){var _13y=function(_13z,_13A){var _13B=E(_13z),_13C=E(_13B.a);if(!E(_13C.a)){if(!E(E(_13B.b).a)){var _13D=__Z;}else{var _13D=new T1(1,new T3(0,0,_13C.b,_13C.c));}var _13E=_13D;}else{var _13E=new T1(1,_13C);}var _13F=new T(function(){var _13G=E(_13A),_13H=E(_13G.b);if(!E(E(_13G.a).a)){if(!E(_13H.a)){return __Z;}else{return new T1(1,_13H);}}else{return new T1(1,_13H);}}),_13I=E(_13E);if(!_13I._){var _13J=new T0(1);}else{var _13K=E(_13F);if(!_13K._){var _13L=new T0(1);}else{var _13M=new T(function(){return E(_13K.a).a;}),_13L=B(_TF(_IQ,B(_Sp(function(_13N){var _13O=E(E(_13N).b);if(E(_13O.a)!=E(_13I.a).a){return false;}else{if(E(_13O.b)!=E(_13v).a){return false;}else{return new F(function(){return _wc(_13O.c,_13M);});}}},_IQ))));}var _13J=_13L;}var _13P=function(_13Q){var _13R=E(_13Q);if(!_13R._){return E(_13J);}else{var _13S=E(_13R.a);return new F(function(){return _K7(_ID,new T3(0,_13S.d,new T3(0,E(_13S.a).a,E(_13S.b).a,E(_13S.c).a),_13S),B(_13P(_13R.b)));});}};return new F(function(){return _13P(B(_Q9(new T2(1,new T(function(){var _13T=E(_13E);if(!_13T._){return __Z;}else{return B(_Qg(_Zd,_13T.a,_13v,_13q));}}),new T2(1,new T(function(){var _13U=E(_13F);if(!_13U._){return __Z;}else{return B(_Qg(_Zd,_13q,_13v,_13U.a));}}),_6)))));});},_13V=E(_13u);if(!_13V._){var _13W=_13V.a;return B(_13y(new T(function(){return B(_V0(_13W,_13p,_13f));}),_13W));}else{var _13X=_13V.a;return B(_13y(_13X,new T(function(){return B(_W3(_13X,_13p,_13f));})));}}),_13Y=B(_10C(new T4(0,new T2(0,_13m.b,_13x),new T(function(){return E(E(_13r).a);}),new T(function(){var _13Z=E(E(_13n).b),_140=E(_13v).a;if(_13Z>=_140){return B(_IE(_140,_13Z,_Q8,_13g));}else{return B(_IE(_13Z,_140,_Q8,_13g));}}),_13p),new T(function(){var _141=E(E(_13b).c);return new T5(0,1,E(_141),new T4(0,_5i,_13g,_13f,_Y5),E(_wv),E(_wv));}),_));return new T2(0,_13Y.a,_13Y.b);}}}});return new T2(0,new T(function(){return E(E(_13j).a);}),new T(function(){return B(_AC(_wv,E(_13j).b));}));},_142=function(_143,_144){return (!E(_143))?false:E(_144);},_145=1,_146=function(_147){return new T1(1,_147);},_148=1,_149=new T(function(){return eval("(function(){return Util.height;})");}),_14a=new T(function(){return eval("(function(){return Util.width;})");}),_14b=function(_){var _14c=E(_4r),_14d=__app1(E(_14a),_14c),_14e=__app1(E(_149),_14c);return new T2(0,_14d,_14e);},_14f=function(_){var _14g=B(_14b(_));return new T(function(){return E(E(_14g).a)/2;});},_14h=new T1(1,_14f),_14i=new T1(0,_ah),_14j=function(_14k,_14l,_14m,_14n,_){var _14o=function(_,_14p){var _14q=function(_,_14r){var _14s=function(_,_14t){var _14u=E(_14n);switch(_14u._){case 0:return new T(function(){var _14v=function(_14w){var _14x=_14w*256,_14y=_14x&4294967295,_14z=function(_14A){var _14B=E(_14r)*256,_14C=_14B&4294967295,_14D=function(_14E){var _14F=function(_14G){var _14H=_14G*256,_14I=_14H&4294967295,_14J=function(_14K){var _14L=E(_14u.a);return (1>_14L)?(0>_14L)?new T4(1,_14A,_14E,_14K,0):new T4(1,_14A,_14E,_14K,_14L):new T4(1,_14A,_14E,_14K,1);};if(_14H>=_14I){if(255>_14I){if(0>_14I){return new F(function(){return _14J(0);});}else{return new F(function(){return _14J(_14I);});}}else{return new F(function(){return _14J(255);});}}else{var _14M=_14I-1|0;if(255>_14M){if(0>_14M){return new F(function(){return _14J(0);});}else{return new F(function(){return _14J(_14M);});}}else{return new F(function(){return _14J(255);});}}},_14N=E(_14t);if(!_14N._){return new F(function(){return _14F(0);});}else{return new F(function(){return _14F(E(_14N.a));});}};if(_14B>=_14C){if(255>_14C){if(0>_14C){return new F(function(){return _14D(0);});}else{return new F(function(){return _14D(_14C);});}}else{return new F(function(){return _14D(255);});}}else{var _14O=_14C-1|0;if(255>_14O){if(0>_14O){return new F(function(){return _14D(0);});}else{return new F(function(){return _14D(_14O);});}}else{return new F(function(){return _14D(255);});}}};if(_14x>=_14y){if(255>_14y){if(0>_14y){return new F(function(){return _14z(0);});}else{return new F(function(){return _14z(_14y);});}}else{return new F(function(){return _14z(255);});}}else{var _14P=_14y-1|0;if(255>_14P){if(0>_14P){return new F(function(){return _14z(0);});}else{return new F(function(){return _14z(_14P);});}}else{return new F(function(){return _14z(255);});}}},_14Q=E(_14p);if(!_14Q._){return B(_14v(0));}else{return B(_14v(E(_14Q.a)));}});case 1:var _14R=B(A1(_14u.a,_)),_14S=_14R;return new T(function(){var _14T=function(_14U){var _14V=_14U*256,_14W=_14V&4294967295,_14X=function(_14Y){var _14Z=E(_14r)*256,_150=_14Z&4294967295,_151=function(_152){var _153=function(_154){var _155=_154*256,_156=_155&4294967295,_157=function(_158){var _159=E(_14S);return (1>_159)?(0>_159)?new T4(1,_14Y,_152,_158,0):new T4(1,_14Y,_152,_158,_159):new T4(1,_14Y,_152,_158,1);};if(_155>=_156){if(255>_156){if(0>_156){return new F(function(){return _157(0);});}else{return new F(function(){return _157(_156);});}}else{return new F(function(){return _157(255);});}}else{var _15a=_156-1|0;if(255>_15a){if(0>_15a){return new F(function(){return _157(0);});}else{return new F(function(){return _157(_15a);});}}else{return new F(function(){return _157(255);});}}},_15b=E(_14t);if(!_15b._){return new F(function(){return _153(0);});}else{return new F(function(){return _153(E(_15b.a));});}};if(_14Z>=_150){if(255>_150){if(0>_150){return new F(function(){return _151(0);});}else{return new F(function(){return _151(_150);});}}else{return new F(function(){return _151(255);});}}else{var _15c=_150-1|0;if(255>_15c){if(0>_15c){return new F(function(){return _151(0);});}else{return new F(function(){return _151(_15c);});}}else{return new F(function(){return _151(255);});}}};if(_14V>=_14W){if(255>_14W){if(0>_14W){return new F(function(){return _14X(0);});}else{return new F(function(){return _14X(_14W);});}}else{return new F(function(){return _14X(255);});}}else{var _15d=_14W-1|0;if(255>_15d){if(0>_15d){return new F(function(){return _14X(0);});}else{return new F(function(){return _14X(_15d);});}}else{return new F(function(){return _14X(255);});}}},_15e=E(_14p);if(!_15e._){return B(_14T(0));}else{return B(_14T(E(_15e.a)));}});case 2:var _15f=rMV(E(E(_14u.a).c)),_15g=E(_15f);return (_15g._==0)?new T(function(){var _15h=function(_15i){var _15j=_15i*256,_15k=_15j&4294967295,_15l=function(_15m){var _15n=E(_14r)*256,_15o=_15n&4294967295,_15p=function(_15q){var _15r=function(_15s){var _15t=_15s*256,_15u=_15t&4294967295,_15v=function(_15w){var _15x=B(A1(_14u.b,new T(function(){return B(_qv(_15g.a));})));return (1>_15x)?(0>_15x)?new T4(1,_15m,_15q,_15w,0):new T4(1,_15m,_15q,_15w,_15x):new T4(1,_15m,_15q,_15w,1);};if(_15t>=_15u){if(255>_15u){if(0>_15u){return new F(function(){return _15v(0);});}else{return new F(function(){return _15v(_15u);});}}else{return new F(function(){return _15v(255);});}}else{var _15y=_15u-1|0;if(255>_15y){if(0>_15y){return new F(function(){return _15v(0);});}else{return new F(function(){return _15v(_15y);});}}else{return new F(function(){return _15v(255);});}}},_15z=E(_14t);if(!_15z._){return new F(function(){return _15r(0);});}else{return new F(function(){return _15r(E(_15z.a));});}};if(_15n>=_15o){if(255>_15o){if(0>_15o){return new F(function(){return _15p(0);});}else{return new F(function(){return _15p(_15o);});}}else{return new F(function(){return _15p(255);});}}else{var _15A=_15o-1|0;if(255>_15A){if(0>_15A){return new F(function(){return _15p(0);});}else{return new F(function(){return _15p(_15A);});}}else{return new F(function(){return _15p(255);});}}};if(_15j>=_15k){if(255>_15k){if(0>_15k){return new F(function(){return _15l(0);});}else{return new F(function(){return _15l(_15k);});}}else{return new F(function(){return _15l(255);});}}else{var _15B=_15k-1|0;if(255>_15B){if(0>_15B){return new F(function(){return _15l(0);});}else{return new F(function(){return _15l(_15B);});}}else{return new F(function(){return _15l(255);});}}},_15C=E(_14p);if(!_15C._){return B(_15h(0));}else{return B(_15h(E(_15C.a)));}}):new T(function(){var _15D=function(_15E){var _15F=_15E*256,_15G=_15F&4294967295,_15H=function(_15I){var _15J=E(_14r)*256,_15K=_15J&4294967295,_15L=function(_15M){var _15N=function(_15O){var _15P=_15O*256,_15Q=_15P&4294967295;if(_15P>=_15Q){return (255>_15Q)?(0>_15Q)?new T4(1,_15I,_15M,0,1):new T4(1,_15I,_15M,_15Q,1):new T4(1,_15I,_15M,255,1);}else{var _15R=_15Q-1|0;return (255>_15R)?(0>_15R)?new T4(1,_15I,_15M,0,1):new T4(1,_15I,_15M,_15R,1):new T4(1,_15I,_15M,255,1);}},_15S=E(_14t);if(!_15S._){return new F(function(){return _15N(0);});}else{return new F(function(){return _15N(E(_15S.a));});}};if(_15J>=_15K){if(255>_15K){if(0>_15K){return new F(function(){return _15L(0);});}else{return new F(function(){return _15L(_15K);});}}else{return new F(function(){return _15L(255);});}}else{var _15T=_15K-1|0;if(255>_15T){if(0>_15T){return new F(function(){return _15L(0);});}else{return new F(function(){return _15L(_15T);});}}else{return new F(function(){return _15L(255);});}}};if(_15F>=_15G){if(255>_15G){if(0>_15G){return new F(function(){return _15H(0);});}else{return new F(function(){return _15H(_15G);});}}else{return new F(function(){return _15H(255);});}}else{var _15U=_15G-1|0;if(255>_15U){if(0>_15U){return new F(function(){return _15H(0);});}else{return new F(function(){return _15H(_15U);});}}else{return new F(function(){return _15H(255);});}}},_15V=E(_14p);if(!_15V._){return B(_15D(0));}else{return B(_15D(E(_15V.a)));}});default:var _15W=rMV(E(E(_14u.a).c)),_15X=E(_15W);if(!_15X._){var _15Y=B(A2(_14u.b,E(_15X.a).a,_)),_15Z=_15Y;return new T(function(){var _160=function(_161){var _162=_161*256,_163=_162&4294967295,_164=function(_165){var _166=E(_14r)*256,_167=_166&4294967295,_168=function(_169){var _16a=function(_16b){var _16c=_16b*256,_16d=_16c&4294967295,_16e=function(_16f){var _16g=E(_15Z);return (1>_16g)?(0>_16g)?new T4(1,_165,_169,_16f,0):new T4(1,_165,_169,_16f,_16g):new T4(1,_165,_169,_16f,1);};if(_16c>=_16d){if(255>_16d){if(0>_16d){return new F(function(){return _16e(0);});}else{return new F(function(){return _16e(_16d);});}}else{return new F(function(){return _16e(255);});}}else{var _16h=_16d-1|0;if(255>_16h){if(0>_16h){return new F(function(){return _16e(0);});}else{return new F(function(){return _16e(_16h);});}}else{return new F(function(){return _16e(255);});}}},_16i=E(_14t);if(!_16i._){return new F(function(){return _16a(0);});}else{return new F(function(){return _16a(E(_16i.a));});}};if(_166>=_167){if(255>_167){if(0>_167){return new F(function(){return _168(0);});}else{return new F(function(){return _168(_167);});}}else{return new F(function(){return _168(255);});}}else{var _16j=_167-1|0;if(255>_16j){if(0>_16j){return new F(function(){return _168(0);});}else{return new F(function(){return _168(_16j);});}}else{return new F(function(){return _168(255);});}}};if(_162>=_163){if(255>_163){if(0>_163){return new F(function(){return _164(0);});}else{return new F(function(){return _164(_163);});}}else{return new F(function(){return _164(255);});}}else{var _16k=_163-1|0;if(255>_16k){if(0>_16k){return new F(function(){return _164(0);});}else{return new F(function(){return _164(_16k);});}}else{return new F(function(){return _164(255);});}}},_16l=E(_14p);if(!_16l._){return B(_160(0));}else{return B(_160(E(_16l.a)));}});}else{return new T(function(){var _16m=function(_16n){var _16o=_16n*256,_16p=_16o&4294967295,_16q=function(_16r){var _16s=E(_14r)*256,_16t=_16s&4294967295,_16u=function(_16v){var _16w=function(_16x){var _16y=_16x*256,_16z=_16y&4294967295;if(_16y>=_16z){return (255>_16z)?(0>_16z)?new T4(1,_16r,_16v,0,1):new T4(1,_16r,_16v,_16z,1):new T4(1,_16r,_16v,255,1);}else{var _16A=_16z-1|0;return (255>_16A)?(0>_16A)?new T4(1,_16r,_16v,0,1):new T4(1,_16r,_16v,_16A,1):new T4(1,_16r,_16v,255,1);}},_16B=E(_14t);if(!_16B._){return new F(function(){return _16w(0);});}else{return new F(function(){return _16w(E(_16B.a));});}};if(_16s>=_16t){if(255>_16t){if(0>_16t){return new F(function(){return _16u(0);});}else{return new F(function(){return _16u(_16t);});}}else{return new F(function(){return _16u(255);});}}else{var _16C=_16t-1|0;if(255>_16C){if(0>_16C){return new F(function(){return _16u(0);});}else{return new F(function(){return _16u(_16C);});}}else{return new F(function(){return _16u(255);});}}};if(_16o>=_16p){if(255>_16p){if(0>_16p){return new F(function(){return _16q(0);});}else{return new F(function(){return _16q(_16p);});}}else{return new F(function(){return _16q(255);});}}else{var _16D=_16p-1|0;if(255>_16D){if(0>_16D){return new F(function(){return _16q(0);});}else{return new F(function(){return _16q(_16D);});}}else{return new F(function(){return _16q(255);});}}},_16E=E(_14p);if(!_16E._){return B(_16m(0));}else{return B(_16m(E(_16E.a)));}});}}},_16F=E(_14m);switch(_16F._){case 0:return new F(function(){return _14s(_,new T1(1,_16F.a));});break;case 1:var _16G=B(A1(_16F.a,_));return new F(function(){return _14s(_,new T1(1,_16G));});break;case 2:var _16H=rMV(E(E(_16F.a).c)),_16I=E(_16H);if(!_16I._){var _16J=new T(function(){return B(A1(_16F.b,new T(function(){return B(_qv(_16I.a));})));});return new F(function(){return _14s(_,new T1(1,_16J));});}else{return new F(function(){return _14s(_,_2o);});}break;default:var _16K=rMV(E(E(_16F.a).c)),_16L=E(_16K);if(!_16L._){var _16M=B(A2(_16F.b,E(_16L.a).a,_));return new F(function(){return _14s(_,new T1(1,_16M));});}else{return new F(function(){return _14s(_,_2o);});}}},_16N=function(_){var _16O=function(_,_16P){var _16Q=E(_14n);switch(_16Q._){case 0:return new T(function(){var _16R=function(_16S){var _16T=_16S*256,_16U=_16T&4294967295,_16V=function(_16W){var _16X=function(_16Y){var _16Z=_16Y*256,_170=_16Z&4294967295,_171=function(_172){var _173=E(_16Q.a);return (1>_173)?(0>_173)?new T4(1,_16W,0,_172,0):new T4(1,_16W,0,_172,_173):new T4(1,_16W,0,_172,1);};if(_16Z>=_170){if(255>_170){if(0>_170){return new F(function(){return _171(0);});}else{return new F(function(){return _171(_170);});}}else{return new F(function(){return _171(255);});}}else{var _174=_170-1|0;if(255>_174){if(0>_174){return new F(function(){return _171(0);});}else{return new F(function(){return _171(_174);});}}else{return new F(function(){return _171(255);});}}},_175=E(_16P);if(!_175._){return new F(function(){return _16X(0);});}else{return new F(function(){return _16X(E(_175.a));});}};if(_16T>=_16U){if(255>_16U){if(0>_16U){return new F(function(){return _16V(0);});}else{return new F(function(){return _16V(_16U);});}}else{return new F(function(){return _16V(255);});}}else{var _176=_16U-1|0;if(255>_176){if(0>_176){return new F(function(){return _16V(0);});}else{return new F(function(){return _16V(_176);});}}else{return new F(function(){return _16V(255);});}}},_177=E(_14p);if(!_177._){return B(_16R(0));}else{return B(_16R(E(_177.a)));}});case 1:var _178=B(A1(_16Q.a,_)),_179=_178;return new T(function(){var _17a=function(_17b){var _17c=_17b*256,_17d=_17c&4294967295,_17e=function(_17f){var _17g=function(_17h){var _17i=_17h*256,_17j=_17i&4294967295,_17k=function(_17l){var _17m=E(_179);return (1>_17m)?(0>_17m)?new T4(1,_17f,0,_17l,0):new T4(1,_17f,0,_17l,_17m):new T4(1,_17f,0,_17l,1);};if(_17i>=_17j){if(255>_17j){if(0>_17j){return new F(function(){return _17k(0);});}else{return new F(function(){return _17k(_17j);});}}else{return new F(function(){return _17k(255);});}}else{var _17n=_17j-1|0;if(255>_17n){if(0>_17n){return new F(function(){return _17k(0);});}else{return new F(function(){return _17k(_17n);});}}else{return new F(function(){return _17k(255);});}}},_17o=E(_16P);if(!_17o._){return new F(function(){return _17g(0);});}else{return new F(function(){return _17g(E(_17o.a));});}};if(_17c>=_17d){if(255>_17d){if(0>_17d){return new F(function(){return _17e(0);});}else{return new F(function(){return _17e(_17d);});}}else{return new F(function(){return _17e(255);});}}else{var _17p=_17d-1|0;if(255>_17p){if(0>_17p){return new F(function(){return _17e(0);});}else{return new F(function(){return _17e(_17p);});}}else{return new F(function(){return _17e(255);});}}},_17q=E(_14p);if(!_17q._){return B(_17a(0));}else{return B(_17a(E(_17q.a)));}});case 2:var _17r=rMV(E(E(_16Q.a).c)),_17s=E(_17r);return (_17s._==0)?new T(function(){var _17t=function(_17u){var _17v=_17u*256,_17w=_17v&4294967295,_17x=function(_17y){var _17z=function(_17A){var _17B=_17A*256,_17C=_17B&4294967295,_17D=function(_17E){var _17F=B(A1(_16Q.b,new T(function(){return B(_qv(_17s.a));})));return (1>_17F)?(0>_17F)?new T4(1,_17y,0,_17E,0):new T4(1,_17y,0,_17E,_17F):new T4(1,_17y,0,_17E,1);};if(_17B>=_17C){if(255>_17C){if(0>_17C){return new F(function(){return _17D(0);});}else{return new F(function(){return _17D(_17C);});}}else{return new F(function(){return _17D(255);});}}else{var _17G=_17C-1|0;if(255>_17G){if(0>_17G){return new F(function(){return _17D(0);});}else{return new F(function(){return _17D(_17G);});}}else{return new F(function(){return _17D(255);});}}},_17H=E(_16P);if(!_17H._){return new F(function(){return _17z(0);});}else{return new F(function(){return _17z(E(_17H.a));});}};if(_17v>=_17w){if(255>_17w){if(0>_17w){return new F(function(){return _17x(0);});}else{return new F(function(){return _17x(_17w);});}}else{return new F(function(){return _17x(255);});}}else{var _17I=_17w-1|0;if(255>_17I){if(0>_17I){return new F(function(){return _17x(0);});}else{return new F(function(){return _17x(_17I);});}}else{return new F(function(){return _17x(255);});}}},_17J=E(_14p);if(!_17J._){return B(_17t(0));}else{return B(_17t(E(_17J.a)));}}):new T(function(){var _17K=function(_17L){var _17M=_17L*256,_17N=_17M&4294967295,_17O=function(_17P){var _17Q=function(_17R){var _17S=_17R*256,_17T=_17S&4294967295;if(_17S>=_17T){return (255>_17T)?(0>_17T)?new T4(1,_17P,0,0,1):new T4(1,_17P,0,_17T,1):new T4(1,_17P,0,255,1);}else{var _17U=_17T-1|0;return (255>_17U)?(0>_17U)?new T4(1,_17P,0,0,1):new T4(1,_17P,0,_17U,1):new T4(1,_17P,0,255,1);}},_17V=E(_16P);if(!_17V._){return new F(function(){return _17Q(0);});}else{return new F(function(){return _17Q(E(_17V.a));});}};if(_17M>=_17N){if(255>_17N){if(0>_17N){return new F(function(){return _17O(0);});}else{return new F(function(){return _17O(_17N);});}}else{return new F(function(){return _17O(255);});}}else{var _17W=_17N-1|0;if(255>_17W){if(0>_17W){return new F(function(){return _17O(0);});}else{return new F(function(){return _17O(_17W);});}}else{return new F(function(){return _17O(255);});}}},_17X=E(_14p);if(!_17X._){return B(_17K(0));}else{return B(_17K(E(_17X.a)));}});default:var _17Y=rMV(E(E(_16Q.a).c)),_17Z=E(_17Y);if(!_17Z._){var _180=B(A2(_16Q.b,E(_17Z.a).a,_)),_181=_180;return new T(function(){var _182=function(_183){var _184=_183*256,_185=_184&4294967295,_186=function(_187){var _188=function(_189){var _18a=_189*256,_18b=_18a&4294967295,_18c=function(_18d){var _18e=E(_181);return (1>_18e)?(0>_18e)?new T4(1,_187,0,_18d,0):new T4(1,_187,0,_18d,_18e):new T4(1,_187,0,_18d,1);};if(_18a>=_18b){if(255>_18b){if(0>_18b){return new F(function(){return _18c(0);});}else{return new F(function(){return _18c(_18b);});}}else{return new F(function(){return _18c(255);});}}else{var _18f=_18b-1|0;if(255>_18f){if(0>_18f){return new F(function(){return _18c(0);});}else{return new F(function(){return _18c(_18f);});}}else{return new F(function(){return _18c(255);});}}},_18g=E(_16P);if(!_18g._){return new F(function(){return _188(0);});}else{return new F(function(){return _188(E(_18g.a));});}};if(_184>=_185){if(255>_185){if(0>_185){return new F(function(){return _186(0);});}else{return new F(function(){return _186(_185);});}}else{return new F(function(){return _186(255);});}}else{var _18h=_185-1|0;if(255>_18h){if(0>_18h){return new F(function(){return _186(0);});}else{return new F(function(){return _186(_18h);});}}else{return new F(function(){return _186(255);});}}},_18i=E(_14p);if(!_18i._){return B(_182(0));}else{return B(_182(E(_18i.a)));}});}else{return new T(function(){var _18j=function(_18k){var _18l=_18k*256,_18m=_18l&4294967295,_18n=function(_18o){var _18p=function(_18q){var _18r=_18q*256,_18s=_18r&4294967295;if(_18r>=_18s){return (255>_18s)?(0>_18s)?new T4(1,_18o,0,0,1):new T4(1,_18o,0,_18s,1):new T4(1,_18o,0,255,1);}else{var _18t=_18s-1|0;return (255>_18t)?(0>_18t)?new T4(1,_18o,0,0,1):new T4(1,_18o,0,_18t,1):new T4(1,_18o,0,255,1);}},_18u=E(_16P);if(!_18u._){return new F(function(){return _18p(0);});}else{return new F(function(){return _18p(E(_18u.a));});}};if(_18l>=_18m){if(255>_18m){if(0>_18m){return new F(function(){return _18n(0);});}else{return new F(function(){return _18n(_18m);});}}else{return new F(function(){return _18n(255);});}}else{var _18v=_18m-1|0;if(255>_18v){if(0>_18v){return new F(function(){return _18n(0);});}else{return new F(function(){return _18n(_18v);});}}else{return new F(function(){return _18n(255);});}}},_18w=E(_14p);if(!_18w._){return B(_18j(0));}else{return B(_18j(E(_18w.a)));}});}}},_18x=E(_14m);switch(_18x._){case 0:return new F(function(){return _16O(_,new T1(1,_18x.a));});break;case 1:var _18y=B(A1(_18x.a,_));return new F(function(){return _16O(_,new T1(1,_18y));});break;case 2:var _18z=rMV(E(E(_18x.a).c)),_18A=E(_18z);if(!_18A._){var _18B=new T(function(){return B(A1(_18x.b,new T(function(){return B(_qv(_18A.a));})));});return new F(function(){return _16O(_,new T1(1,_18B));});}else{return new F(function(){return _16O(_,_2o);});}break;default:var _18C=rMV(E(E(_18x.a).c)),_18D=E(_18C);if(!_18D._){var _18E=B(A2(_18x.b,E(_18D.a).a,_));return new F(function(){return _16O(_,new T1(1,_18E));});}else{return new F(function(){return _16O(_,_2o);});}}},_18F=E(_14l);switch(_18F._){case 0:return new F(function(){return _14q(_,_18F.a);});break;case 1:var _18G=B(A1(_18F.a,_));return new F(function(){return _14q(_,_18G);});break;case 2:var _18H=rMV(E(E(_18F.a).c)),_18I=E(_18H);if(!_18I._){var _18J=new T(function(){return B(A1(_18F.b,new T(function(){return E(E(_18I.a).a);})));});return new F(function(){return _14q(_,_18J);});}else{return new F(function(){return _16N(_);});}break;default:var _18K=rMV(E(E(_18F.a).c)),_18L=E(_18K);if(!_18L._){var _18M=B(A2(_18F.b,E(_18L.a).a,_));return new F(function(){return _14q(_,_18M);});}else{return new F(function(){return _16N(_);});}}},_18N=E(_14k);switch(_18N._){case 0:return new F(function(){return _14o(_,new T1(1,_18N.a));});break;case 1:var _18O=B(A1(_18N.a,_));return new F(function(){return _14o(_,new T1(1,_18O));});break;case 2:var _18P=rMV(E(E(_18N.a).c)),_18Q=E(_18P);if(!_18Q._){var _18R=new T(function(){return B(A1(_18N.b,new T(function(){return B(_qv(_18Q.a));})));});return new F(function(){return _14o(_,new T1(1,_18R));});}else{return new F(function(){return _14o(_,_2o);});}break;default:var _18S=rMV(E(E(_18N.a).c)),_18T=E(_18S);if(!_18T._){var _18U=B(A2(_18N.b,E(_18T.a).a,_));return new F(function(){return _14o(_,new T1(1,_18U));});}else{return new F(function(){return _14o(_,_2o);});}}},_18V=")",_18W=new T2(1,_18V,_6),_18X=",",_18Y="rgba(",_18Z=new T(function(){return toJSStr(_6);}),_190="rgb(",_191=function(_192){var _193=E(_192);if(!_193._){var _194=jsCat(new T2(1,_190,new T2(1,new T(function(){return String(_193.a);}),new T2(1,_18X,new T2(1,new T(function(){return String(_193.b);}),new T2(1,_18X,new T2(1,new T(function(){return String(_193.c);}),_18W)))))),E(_18Z));return E(_194);}else{var _195=jsCat(new T2(1,_18Y,new T2(1,new T(function(){return String(_193.a);}),new T2(1,_18X,new T2(1,new T(function(){return String(_193.b);}),new T2(1,_18X,new T2(1,new T(function(){return String(_193.c);}),new T2(1,_18X,new T2(1,new T(function(){return String(_193.d);}),_18W)))))))),E(_18Z));return E(_195);}},_196=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_197="fillStyle",_198=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_199=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_19a=function(_19b,_19c){return new T2(1,new T2(0,function(_19d,_){var _19e=E(_19b),_19f=B(_14j(_19e.a,_19e.b,_19e.c,_19e.d,_)),_19g=E(_19d),_19h=__app3(E(_199),_19g,E(_197),B(_191(_19f))),_19i=__app1(E(_196),_19g),_19j=B(A3(E(_19c).b,_19g,_cm,_)),_19k=__app1(E(_198),_19g);return new F(function(){return _qV(_);});},_7),_14i);},_19l=function(_19m,_19n,_19o,_19p){var _19q=function(_19r,_19s,_19t,_){var _19u=function(_19v,_19w,_19x,_){var _19y=function(_19z,_19A,_19B,_){return new F(function(){return _qx(_19p,function(_19C,_19D,_19E,_){var _19F=E(_19r),_19G=E(_19v),_19H=E(_19D),_19I=E(_19E),_19J=__app4(E(_qX),_19F,_19G,_19H,_19I),_19K=_19F+E(_19z),_19L=E(_uk),_19M=__app4(_19L,_19K,_19G,_19H,_19I),_19N=_19G+E(_19C),_19O=__app4(_19L,_19K,_19N,_19H,_19I),_19P=__app4(_19L,_19F,_19N,_19H,_19I),_19Q=__app4(_19L,_19F,_19G,_19H,_19I);return new F(function(){return _qV(_);});},_19A,_19B,_);});};return new F(function(){return _qx(_19o,_19y,_19w,_19x,_);});};return new F(function(){return _qx(_19n,_19u,_19s,_19t,_);});},_19R=function(_19S,_){var _19T=E(_19S),_19U=function(_19V,_){var _19W=function(_19X,_){var _19Y=function(_19Z,_){var _1a0=function(_1a1,_){return new T(function(){var _1a2=E(_19Z),_1a3=E(_19T.a)-E(_19V)-_1a2/2,_1a4=function(_1a5){var _1a6=E(_1a1),_1a7=E(_19T.b)-E(_19X)-_1a6/2;return (_1a7!=0)?(_1a7<=0)? -_1a7<_1a6/2:_1a7<_1a6/2:0<_1a6/2;};if(_1a3!=0){if(_1a3<=0){if( -_1a3>=_1a2/2){return false;}else{return B(_1a4(_));}}else{if(_1a3>=_1a2/2){return false;}else{return B(_1a4(_));}}}else{if(0>=_1a2/2){return false;}else{return B(_1a4(_));}}});};return new F(function(){return _qK(_19p,_1a0,_);});};return new F(function(){return _qK(_19o,_19Y,_);});};return new F(function(){return _qK(_19n,_19W,_);});};return new F(function(){return _qK(_19m,_19U,_);});};return new T3(0,_19R,function(_rD,_rE,_){return new F(function(){return _qx(_19m,_19q,_rD,_rE,_);});},_7);},_1a8=function(_){var _1a9=B(_14b(_));return new T(function(){return E(E(_1a9).b);});},_1aa=new T1(1,_1a8),_1ab=0,_1ac=new T1(0,_1ab),_1ad=new T(function(){var _1ae=B(_19l(_1ac,_1ac,_14h,_1aa));return new T3(0,_1ae.a,_1ae.b,_1ae.c);}),_1af=1,_1ag=new T1(0,_1af),_1ah=new T4(0,_1ag,_1ag,_1ag,_1ag),_1ai=new T(function(){return B(_19a(_1ah,_1ad));}),_1aj=10,_1ak=new T1(0,_6),_1al=new T1(0,_ah),_1am=new T(function(){return B(unCStr("head"));}),_1an=new T(function(){return B(_f4(_1am));}),_1ao=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_1ap=function(_1aq,_){var _1ar=__app1(E(_1ao),E(_1aq));return new F(function(){return _qV(_);});},_1as=new T2(0,_1ap,_7),_1at=new T2(1,_1as,_14i),_1au=function(_1av){return E(_1at);},_1aw=new T1(0,_1au),_1ax=new T(function(){return eval("(function(ctx){ctx.clip();})");}),_1ay=new T(function(){return eval("(function(ctx){ctx.save();})");}),_1az=function(_1aA,_1aB){return new T2(1,new T2(0,function(_1aC,_){var _1aD=E(_1aC),_1aE=__app1(E(_1ay),_1aD),_1aF=__app1(E(_196),_1aD),_1aG=B(A3(E(_1aA).b,_1aD,_cm,_)),_1aH=__app1(E(_1ax),_1aD);return new F(function(){return _qV(_);});},_7),new T2(1,new T2(1,_14i,new T1(0,function(_1aI){return E(_1aB);})),_1aw));},_1aJ=function(_1aK,_1aL){return new F(function(){return A1(_1aL,new T2(0,_7,_1aK));});},_1aM=function(_1aN,_1aO,_1aP){return new F(function(){return _1aJ(_1aO,_1aP);});},_1aQ=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1aR=new T(function(){return B(err(_1aQ));}),_1aS=0,_1aT=0,_1aU=0.15,_1aV=new T1(0,_1aU),_1aW=1,_1aX=new T1(0,_1aW),_1aY=new T4(0,_1aV,_1aV,_1aV,_1aX),_1aZ=new T2(1,_eC,_6),_1b0=2,_1b1=new T1(0,_1b0),_1b2=0.2,_1b3=new T1(0,_1b2),_1b4=new T4(0,_1ac,_1aX,_1b3,_1aX),_1b5="mplus",_1b6=new T1(0,_1aj),_1b7=function(_1b8,_1b9,_){var _1ba=E(_1b8);switch(_1ba._){case 0:return new F(function(){return A2(_1b9,_1ba.a,_);});break;case 1:var _1bb=B(A1(_1ba.a,_));return new F(function(){return A2(_1b9,_1bb,_);});break;case 2:var _1bc=rMV(E(E(_1ba.a).c)),_1bd=E(_1bc);if(!_1bd._){var _1be=new T(function(){return B(A1(_1ba.b,new T(function(){return B(_qv(_1bd.a));})));});return new F(function(){return A2(_1b9,_1be,_);});}else{return _7;}break;default:var _1bf=rMV(E(E(_1ba.a).c)),_1bg=E(_1bf);if(!_1bg._){var _1bh=B(A2(_1ba.b,E(_1bg.a).a,_));return new F(function(){return A2(_1b9,_1bh,_);});}else{return _7;}}},_1bi="lineWidth",_1bj="strokeStyle",_1bk=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_1bl=function(_1bm,_1bn,_1bo){var _1bp=function(_1bq,_){return new F(function(){return _1b7(_1bm,function(_1br,_){var _1bs=E(_1bn),_1bt=B(_14j(_1bs.a,_1bs.b,_1bs.c,_1bs.d,_)),_1bu=E(_1bq),_1bv=E(_199),_1bw=__app3(_1bv,_1bu,E(_1bj),B(_191(_1bt))),_1bx=String(E(_1br)),_1by=__app3(_1bv,_1bu,E(_1bi),_1bx),_1bz=__app1(E(_196),_1bu),_1bA=B(A3(E(_1bo).b,_1bu,_5i,_)),_1bB=__app1(E(_1bk),_1bu);return new F(function(){return _qV(_);});},_);});};return new T2(1,new T2(0,_1bp,_7),_14i);},_1bC=function(_1bD){var _1bE=E(_1bD);if(!_1bE._){return E(_oN);}else{var _1bF=E(_1bE.a),_1bG=E(_1bF.c),_1bH=_1bG.a,_1bI=_1bG.b,_1bJ=E(_1bF.d),_1bK=new T(function(){return B(_1bC(_1bE.b));}),_1bL=function(_1bM){return E(_1bK);},_1bN=new T(function(){var _1bO=new T(function(){var _1bP=new T(function(){return B(A3(_f8,_eY,new T2(1,function(_1bQ){return new F(function(){return _fi(0,_1bF.a,_1bQ);});},new T2(1,function(_1bR){return new F(function(){return _fi(0,_1bF.b,_1bR);});},_6)),_1aZ));}),_1bS=B(_vm(_1b5,new T1(0,new T2(1,_eD,_1bP)),_1aS,_1aT,new T1(0,_1bH),new T1(0,_1bI),_1b6));return new T3(0,_1bS.a,_1bS.b,_1bS.c);});return B(_19a(_1aY,_1bO));}),_1bT=B(_1bl(_1b1,_1b4,new T(function(){var _1bU=B(_ur(new T2(0,new T1(0,_1bH),new T1(0,_1bI)),new T2(0,new T1(0,_1bJ.a),new T1(0,_1bJ.b))));return new T3(0,_1bU.a,_1bU.b,_1bU.c);})));if(!_1bT._){var _1bV=E(_1bN);return (_1bV._==0)?E(_1bK):new T2(1,_1bV.a,new T2(1,_1bV.b,new T1(0,_1bL)));}else{return new T2(1,_1bT.a,new T2(1,new T2(1,_1bT.b,new T1(0,function(_1bW){return E(_1bN);})),new T1(0,_1bL)));}}},_1bX=function(_1bY){var _1bZ=E(_1bY);if(!_1bZ._){return __Z;}else{var _1c0=E(_1bZ.a);return new T2(1,_1c0.a,new T2(1,_1c0.b,new T(function(){return B(_1bX(_1bZ.b));})));}},_1c1=new T4(0,_1aX,_1ac,_1ac,_1aX),_1c2=5,_1c3=new T1(0,_1c2),_1c4=function(_1c5,_1c6){while(1){var _1c7=B((function(_1c8,_1c9){var _1ca=E(_1c9);if(!_1ca._){var _1cb=_1ca.e,_1cc=E(_1ca.b),_1cd=new T(function(){var _1ce=E(_1ca.c);if(_1ce._==1){var _1cf=E(_1ce.a),_1cg=_1cf.a,_1ch=_1cf.b,_1ci=new T(function(){return B(_1c4(_1c8,_1cb));}),_1cj=function(_1ck){return E(_1ci);},_1cl=new T(function(){var _1cm=new T(function(){var _1cn=new T(function(){return B(A3(_f8,_eY,new T2(1,function(_1co){return new F(function(){return _fi(0,E(_1cc.a),_1co);});},new T2(1,function(_1cp){return new F(function(){return _fi(0,E(_1cc.b),_1cp);});},_6)),_1aZ));}),_1cq=B(_vm(_1b5,new T1(0,new T2(1,_eD,_1cn)),_1aS,_1aT,new T1(0,new T(function(){return E(_1cg)-10;})),new T1(0,new T(function(){return E(_1ch)-10;})),_1b6));return new T3(0,_1cq.a,_1cq.b,_1cq.c);});return B(_19a(_1aY,_1cm));}),_1cr=B(_19a(_1c1,new T(function(){var _1cs=B(_qZ(new T1(0,_1cg),new T1(0,_1ch),_1c3));return new T3(0,_1cs.a,_1cs.b,_1cs.c);})));if(!_1cr._){var _1ct=E(_1cl);if(!_1ct._){return E(_1ci);}else{return new T2(1,_1ct.a,new T2(1,_1ct.b,new T1(0,_1cj)));}}else{return new T2(1,_1cr.a,new T2(1,new T2(1,_1cr.b,new T1(0,function(_1cu){return E(_1cl);})),new T1(0,_1cj)));}}else{return B(_1c4(_1c8,_1cb));}},1);_1c5=_1cd;_1c6=_1ca.d;return __continue;}else{return E(_1c8);}})(_1c5,_1c6));if(_1c7!=__continue){return _1c7;}}},_1cv=function(_1cw){return new F(function(){return _fi(0,E(_1cw),_6);});},_1cx=function(_1cy,_1cz){var _1cA=E(_1cy);if(!_1cA._){return E(_1ak);}else{var _1cB=E(_1cz);if(!_1cB._){return E(_1ak);}else{var _1cC=E(_1cB.a),_1cD=_1cC.a,_1cE=_1cC.b,_1cF=new T(function(){return B(_1cx(_1cA.b,_1cB.b));}),_1cG=function(_1cH){var _1cI=E(_1cF);return (_1cI._==0)?new T1(0,new T2(1,_1cH,_1cI.a)):new T2(1,_1cI.a,new T2(1,_1cI.b,new T1(0,function(_1cJ){return new T1(0,new T2(1,_1cH,_1cJ));})));},_1cK=new T(function(){var _1cL=new T(function(){var _1cM=B(_vm(_1b5,new T1(0,new T(function(){return B(_1cv(_1cA.a));})),_1aS,_1aT,new T1(0,new T(function(){return E(_1cD)-10;})),new T1(0,new T(function(){return E(_1cE)-10;})),_1b6));return new T3(0,_1cM.a,_1cM.b,_1cM.c);});return B(_19a(_1aY,_1cL));}),_1cN=B(_19a(_1aY,new T(function(){var _1cO=B(_qZ(new T1(0,_1cD),new T1(0,_1cE),_1c3));return new T3(0,_1cO.a,_1cO.b,_1cO.c);})));if(!_1cN._){var _1cP=E(_1cK);if(!_1cP._){return new F(function(){return _1cG(_1cP.a);});}else{return new T2(1,_1cP.a,new T2(1,_1cP.b,new T1(0,_1cG)));}}else{return new T2(1,_1cN.a,new T2(1,new T2(1,_1cN.b,new T1(0,function(_1cQ){return E(_1cK);})),new T1(0,_1cG)));}}}},_1cR=new T(function(){return B(_Y6(0,2147483647));}),_1cS=function(_1cT){var _1cU=E(_1cT);if(!_1cU._){return __Z;}else{return new F(function(){return _2(B(_1cS(_1cU.a)),new T2(1,_1cU.b,new T(function(){return B(_1cS(_1cU.c));})));});}},_1cV=function(_1cW,_1cX){return new F(function(){return A1(_1cW,_1cX);});},_1cY=function(_1aO,_1aP){return new F(function(){return _1cV(_1aO,_1aP);});},_1cZ=function(_1d0,_1d1){var _1d2=E(E(_1d0).a)-E(E(_1d1).a);return (_1d2!=0)?(_1d2<=0)? -_1d2<5:_1d2<5:true;},_1d3=0.5,_1d4=new T1(0,_1d3),_1d5=new T4(0,_1ac,_1d4,_1aX,_1aX),_1d6=function(_1d7,_1d8){var _1d9=E(E(_1d7).a),_1da=E(E(_1d8).a);return (_1d9>=_1da)?(_1d9!=_1da)?2:1:0;},_1db=new T4(0,_1ab,_1ab,_se,_5i),_1dc=new T2(0,_1ab,_1db),_1dd=new T2(0,_1dc,_6),_1de=function(_1df,_1dg){var _1dh=E(E(_1df).b)-E(E(_1dg).b);return (_1dh!=0)?(_1dh<=0)? -_1dh<5:_1dh<5:true;},_1di=400,_1dj=function(_1dk,_1dl,_1dm){var _1dn=new T(function(){return new T1(0,B(_p6(_1dl,_1dm,_p4)));}),_1do=function(_1dp){return new T1(1,new T2(1,new T(function(){return B(A1(_1dp,_7));}),new T2(1,_1dn,_6)));};return new F(function(){return A2(_rJ,_1dk,_1do);});},_1dq=function(_1dr,_1ds,_1dt,_){var _1du=__app2(E(_v9),E(_1ds),E(_1dt));return new F(function(){return _qV(_);});},_1dv=function(_1dw,_1dx,_1dy,_1dz,_1dA,_1dB,_1dC){var _1dD=function(_1dE,_1dF,_1dG,_){var _1dH=function(_1dI,_1dJ,_1dK,_){var _1dL=function(_1dM,_1dN,_1dO,_){var _1dP=function(_1dQ,_1dR,_1dS,_){return new F(function(){return _qx(_1dA,function(_1dT,_1dU,_1dV,_){return new F(function(){return _qx(_1dB,_1dq,_1dU,_1dV,_);});},_1dR,_1dS,_);});};return new F(function(){return _qx(_1dz,_1dP,_1dN,_1dO,_);});};return new F(function(){return _qx(_1dy,_1dL,_1dJ,_1dK,_);});};return new F(function(){return _qx(_1dx,_1dH,_1dF,_1dG,_);});},_1dW=function(_1dX,_){var _1dY=E(_1dX),_1dZ=_1dY.a,_1e0=_1dY.b,_1e1=function(_1e2,_){var _1e3=function(_1e4,_){var _1e5=function(_1e6,_){var _1e7=function(_1e8,_){var _1e9=function(_1ea,_){var _1eb=function(_1ec){var _1ed=new T(function(){return E(_1e4)*E(_1e8)-E(_1e2)*E(_1ea);});return new F(function(){return A1(_1dC,new T2(0,new T(function(){var _1ee=E(_1e4),_1ef=E(_1ea);return ( -(_1ee*E(_1ec))+_1ee*E(_1e0)+_1ef*E(_1e6)-_1ef*E(_1dZ))/E(_1ed);}),new T(function(){var _1eg=E(_1e2),_1eh=E(_1e8);return (_1eg*E(_1ec)-_1eg*E(_1e0)-_1eh*E(_1e6)+_1eh*E(_1dZ))/E(_1ed);})));});};return new F(function(){return _qK(_1dB,_1eb,_);});};return new F(function(){return _qK(_1dA,_1e9,_);});};return new F(function(){return _qK(_1dz,_1e7,_);});};return new F(function(){return _qK(_1dy,_1e5,_);});};return new F(function(){return _qK(_1dx,_1e3,_);});};return new F(function(){return _qK(_1dw,_1e1,_);});};return new T3(0,_1dW,function(_rD,_rE,_){return new F(function(){return _qx(_1dw,_1dD,_rD,_rE,_);});},_7);},_1ei=function(_1ej,_1ek,_1el){var _1em=E(_1ek),_1en=E(_1el);switch(_1en._){case 0:var _1eo=_1en.a,_1ep=_1en.b,_1eq=_1en.c,_1er=_1en.d,_1es=_1ep>>>0;if(((_1ej>>>0&((_1es-1>>>0^4294967295)>>>0^_1es)>>>0)>>>0&4294967295)==_1eo){return ((_1ej>>>0&_1es)>>>0==0)?new T4(0,_1eo,_1ep,E(B(_1ei(_1ej,_1em,_1eq))),E(_1er)):new T4(0,_1eo,_1ep,E(_1eq),E(B(_1ei(_1ej,_1em,_1er))));}else{var _1et=(_1ej>>>0^_1eo>>>0)>>>0,_1eu=(_1et|_1et>>>1)>>>0,_1ev=(_1eu|_1eu>>>2)>>>0,_1ew=(_1ev|_1ev>>>4)>>>0,_1ex=(_1ew|_1ew>>>8)>>>0,_1ey=(_1ex|_1ex>>>16)>>>0,_1ez=(_1ey^_1ey>>>1)>>>0&4294967295,_1eA=_1ez>>>0;return ((_1ej>>>0&_1eA)>>>0==0)?new T4(0,(_1ej>>>0&((_1eA-1>>>0^4294967295)>>>0^_1eA)>>>0)>>>0&4294967295,_1ez,E(new T2(1,_1ej,_1em)),E(_1en)):new T4(0,(_1ej>>>0&((_1eA-1>>>0^4294967295)>>>0^_1eA)>>>0)>>>0&4294967295,_1ez,E(_1en),E(new T2(1,_1ej,_1em)));}break;case 1:var _1eB=_1en.a;if(_1ej!=_1eB){var _1eC=(_1ej>>>0^_1eB>>>0)>>>0,_1eD=(_1eC|_1eC>>>1)>>>0,_1eE=(_1eD|_1eD>>>2)>>>0,_1eF=(_1eE|_1eE>>>4)>>>0,_1eG=(_1eF|_1eF>>>8)>>>0,_1eH=(_1eG|_1eG>>>16)>>>0,_1eI=(_1eH^_1eH>>>1)>>>0&4294967295,_1eJ=_1eI>>>0;return ((_1ej>>>0&_1eJ)>>>0==0)?new T4(0,(_1ej>>>0&((_1eJ-1>>>0^4294967295)>>>0^_1eJ)>>>0)>>>0&4294967295,_1eI,E(new T2(1,_1ej,_1em)),E(_1en)):new T4(0,(_1ej>>>0&((_1eJ-1>>>0^4294967295)>>>0^_1eJ)>>>0)>>>0&4294967295,_1eI,E(_1en),E(new T2(1,_1ej,_1em)));}else{return new T2(1,_1ej,_1em);}break;default:return new T2(1,_1ej,_1em);}},_1eK=6,_1eL=4,_1eM=0,_1eN=2,_1eO=1,_1eP=3,_1eQ=5,_1eR=new T1(0,_ah),_1eS=function(_1eT,_1eU){return new F(function(){return A1(_1eU,new T2(0,_7,_1eT));});},_1eV=new T1(1,_6),_1eW=0,_1eX=new T4(0,_1eW,_1eW,_se,_5i),_1eY=new T2(0,_1eW,_1eX),_1eZ=new T2(0,_1eY,_6),_1f0=1,_1f1=new T4(0,_1f0,_1f0,_se,_5i),_1f2=new T2(0,_1f0,_1f1),_1f3=new T2(0,_1f2,_6),_1f4=function(_1f5){return E(E(_1f5).c);},_1f6=new T1(1,_6),_1f7=function(_1f8){var _1f9=function(_){var _1fa=nMV(_1f6);return new T(function(){return B(A1(_1f8,_1fa));});};return new T1(0,_1f9);},_1fb=function(_1fc,_1fd){var _1fe=new T(function(){return B(_1f4(_1fc));}),_1ff=B(_rF(_1fc)),_1fg=function(_1fh){var _1fi=new T(function(){return B(A1(_1fe,new T(function(){return B(A1(_1fd,_1fh));})));});return new F(function(){return A3(_rH,_1ff,_1fi,new T(function(){return B(A2(_b1,_1ff,_1fh));}));});};return new F(function(){return A3(_ap,_1ff,new T(function(){return B(A2(_rJ,_1fc,_1f7));}),_1fg);});},_1fj=function(_1fk,_1fl,_1fm,_1fn){var _1fo=new T(function(){return B(A1(_1fk,_1eN));}),_1fp=new T(function(){return B(A1(_1fk,_1eM));}),_1fq=new T(function(){return B(A1(_1fk,_1eL));}),_1fr=new T(function(){return B(_1fb(_4l,_1fn));}),_1fs=new T(function(){return B(A1(_1fk,_1eK));}),_1ft=new T(function(){return B(A1(_1fk,_1eQ));}),_1fu=new T(function(){return B(A1(_1fk,_1eP));}),_1fv=new T(function(){return B(A1(_1fk,_1eO));}),_1fw=function(_1fx){var _1fy=new T(function(){return B(A1(_1fr,_1fx));}),_1fz=function(_1fA){var _1fB=function(_1fC){var _1fD=E(_1fC),_1fE=_1fD.a,_1fF=_1fD.b,_1fG=new T(function(){var _1fH=E(_1fo);if(!_1fH._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fH.a));}}),_1fI=new T(function(){var _1fJ=E(_1fp);if(!_1fJ._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fJ.a));}}),_1fK=new T(function(){var _1fL=E(_1fq);if(!_1fL._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fL.a));}}),_1fM=new T(function(){var _1fN=E(_1fs);if(!_1fN._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fN.a));}}),_1fO=new T(function(){var _1fP=E(_1ft);if(!_1fP._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fP.a));}}),_1fQ=new T(function(){var _1fR=E(_1fu);if(!_1fR._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fR.a));}}),_1fS=new T(function(){var _1fT=E(_1fv);if(!_1fT._){return E(_1eS);}else{return B(_1dj(_4l,_1fE,_1fT.a));}}),_1fU=function(_){var _1fV=nMV(_1f3),_1fW=_1fV,_1fX=function(_){var _1fY=nMV(_1eZ),_1fZ=_1fY,_1g0=function(_){var _1g1=nMV(_1eZ),_1g2=_1g1,_1g3=function(_){var _1g4=nMV(_1eZ),_1g5=_1g4,_1g6=function(_){var _1g7=nMV(_1f3),_1g8=_1g7,_1g9=function(_){var _1ga=nMV(_1eZ),_1gb=_1ga,_1gc=function(_1gd,_1ge,_1gf,_1gg,_1gh,_1gi){var _1gj=new T(function(){return B(_tk(_1fW,_1gd));}),_1gk=new T(function(){return B(_tk(_1fZ,_1ge));}),_1gl=new T(function(){return B(_tk(_1g2,_1gf));}),_1gm=new T(function(){return B(_tk(_1g5,_1gg));}),_1gn=new T(function(){return B(_tk(_1g8,_1gh));}),_1go=new T(function(){return B(_tk(_1gb,_1gi));}),_1gp=function(_1gq){var _1gr=new T(function(){return B(A1(_1gj,_1gq));}),_1gs=function(_1gt){var _1gu=function(_1gv){return new F(function(){return A1(_1gt,new T2(0,_7,E(_1gv).b));});},_1gw=function(_1gx){return new F(function(){return A2(_1go,E(_1gx).b,_1gu);});},_1gy=function(_1gz){return new F(function(){return A2(_1gn,E(_1gz).b,_1gw);});},_1gA=function(_1gB){return new F(function(){return A2(_1gm,E(_1gB).b,_1gy);});},_1gC=function(_1gD){return new F(function(){return A2(_1gl,E(_1gD).b,_1gA);});};return new F(function(){return A1(_1gr,function(_1gE){return new F(function(){return A2(_1gk,E(_1gE).b,_1gC);});});});};return E(_1gs);};return E(_1gp);},_1gF=new T2(1,new T2(2,_1gc,_7),_1eR),_1gG=new T(function(){var _1gH=E(_1fm);if(!_1gH._){return E(_1gF);}else{return new T2(1,_1gH.a,new T2(1,_1gH.b,new T1(0,function(_1gI){return E(_1gF);})));}}),_1gJ=new T(function(){var _1gK=B(_1dv(new T2(2,new T3(0,_tj,_1cV,_1fW),_2E),new T2(2,new T3(0,_tj,_1cV,_1fZ),_2E),new T2(2,new T3(0,_tj,_1cV,_1g2),_2E),new T2(2,new T3(0,_tj,_1cV,_1g5),_2E),new T2(2,new T3(0,_tj,_1cV,_1g8),_2E),new T2(2,new T3(0,_tj,_1cV,_1gb),_2E),E(_1fl).a));return new T3(0,_1gK.a,_1gK.b,_1gK.c);}),_1gL=function(_){var _1gM=nMV(_1eV),_1gN=_1gM,_1gO=new T(function(){var _1gP=function(_1gQ){return new F(function(){return _1gR(E(_1gQ).b);});},_1gS=function(_1gT){var _1gU=new T(function(){return B(A2(_1fS,_1gT,_1gV));}),_1gW=new T(function(){return B(A2(_1fG,_1gT,_1gP));}),_1gX=new T(function(){return B(A2(_1fQ,_1gT,_1gY));}),_1gZ=new T(function(){return B(_1gS(_1gT));}),_1h0=function(_1h1){var _1h2=E(_1h1);if(!_1h2._){return (!E(_1h2.a))?E(_1gZ):E(_1gX);}else{var _1h3=function(_){var _1h4=B(A2(E(_1gJ).a,_1h2.a,_));return new T(function(){if(!E(_1h4)){return E(_1gW);}else{return E(_1gU);}});};return new T1(0,_1h3);}};return new T1(0,B(_pi(_1gN,_1h0)));},_1gV=function(_1h5){return new F(function(){return _1gS(E(_1h5).b);});},_1gR=function(_1h6){var _1h7=new T(function(){return B(_1gR(_1h6));}),_1h8=new T(function(){return B(A2(_1fI,_1h6,_1gV));}),_1h9=function(_1ha){var _1hb=E(_1ha);if(!_1hb._){return E(_1h7);}else{var _1hc=function(_){var _1hd=B(A2(E(_1gJ).a,_1hb.a,_));return new T(function(){if(!E(_1hd)){return E(_1h7);}else{return E(_1h8);}});};return new T1(0,_1hc);}};return new T1(0,B(_pi(_1gN,_1h9)));},_1he=function(_1hf){var _1hg=new T(function(){return B(A2(_1fK,_1hf,_1gY));}),_1hh=new T(function(){return B(A2(_1fG,_1hf,_1hi));}),_1hj=new T(function(){return B(_1he(_1hf));}),_1hk=new T(function(){return B(A2(_1fO,_1hf,_1gV));}),_1hl=function(_1hm){var _1hn=E(_1hm);if(!_1hn._){return (!E(_1hn.a))?E(_1hk):E(_1hj);}else{var _1ho=function(_){var _1hp=B(A2(E(_1gJ).a,_1hn.a,_));return new T(function(){if(!E(_1hp)){return E(_1hh);}else{return E(_1hg);}});};return new T1(0,_1ho);}};return new T1(0,B(_pi(_1gN,_1hl)));},_1gY=function(_1hq){return new F(function(){return _1he(E(_1hq).b);});},_1hr=function(_1hs){var _1ht=new T(function(){return B(A2(_1fI,_1hs,_1gY));}),_1hu=new T(function(){return B(A2(_1fK,_1hs,_1hi));}),_1hv=new T(function(){return B(_1hr(_1hs));}),_1hw=new T(function(){return B(A2(_1fM,_1hs,_1gP));}),_1hx=function(_1hy){var _1hz=E(_1hy);if(!_1hz._){return (!E(_1hz.a))?E(_1hw):E(_1hv);}else{var _1hA=function(_){var _1hB=B(A2(E(_1gJ).a,_1hz.a,_));return new T(function(){if(!E(_1hB)){return E(_1hu);}else{return E(_1ht);}});};return new T1(0,_1hA);}};return new T1(0,B(_pi(_1gN,_1hx)));},_1hi=function(_1hC){return new F(function(){return _1hr(E(_1hC).b);});};return B(_1gR(_1fF));}),_1hD=new T(function(){var _1hE=function(_1hF){var _1hG=E(_1hF);return new F(function(){return A1(_1fA,new T2(0,new T(function(){return new T3(0,E(_1hG.a),_1gG,E(_1fE));}),_1hG.b));});},_1hH=function(_1hI,_1hJ,_1hK){var _1hL=new T(function(){return E(E(_1hI).d);}),_1hM=new T(function(){return E(E(_1hL).a);}),_1hN=new T(function(){var _1hO=E(_1hI);return new T4(0,E(_1hO.a),_1hO.b,E(_1hO.c),E(new T2(0,new T(function(){return E(_1hM)+1|0;}),new T(function(){return B(_1ei(E(_1hM),_1gN,E(_1hL).b));}))));});return new F(function(){return A1(_1hK,new T2(0,new T2(0,_1hM,_1hN),_1hJ));});};return B(A(_rS,[_4l,_1fF,_1hH,_1fF,_1hE]));});return new T1(1,new T2(1,_1hD,new T2(1,_1gO,_6)));};return new T1(0,_1gL);};return new T1(0,_1g9);};return new T1(0,_1g6);};return new T1(0,_1g3);};return new T1(0,_1g0);};return new T1(0,_1fX);};return new T1(0,_1fU);};return new F(function(){return A1(_1fy,_1fB);});};return E(_1fz);};return E(_1fw);},_1hP=function(_1hQ,_1hR,_1hS){while(1){var _1hT=E(_1hS);if(!_1hT._){return false;}else{if(!B(A2(_1hQ,_1hT.a,_1hR))){_1hS=_1hT.b;continue;}else{return true;}}}},_1hU=function(_1hV,_1hW){var _1hX=function(_1hY,_1hZ){while(1){var _1i0=B((function(_1i1,_1i2){var _1i3=E(_1i1);if(!_1i3._){return __Z;}else{var _1i4=_1i3.a,_1i5=_1i3.b;if(!B(_1hP(_1hV,_1i4,_1i2))){return new T2(1,_1i4,new T(function(){return B(_1hX(_1i5,new T2(1,_1i4,_1i2)));}));}else{var _1i6=_1i2;_1hY=_1i5;_1hZ=_1i6;return __continue;}}})(_1hY,_1hZ));if(_1i0!=__continue){return _1i0;}}};return new F(function(){return _1hX(_1hW,_6);});},_1i7=function(_1i8){return E(E(_1i8).a);},_1i9=function(_1ia){return E(E(_1ia).a);},_1ib=function(_1ic,_1id,_1ie){var _1if=E(_1id),_1ig=E(_1ie),_1ih=new T(function(){var _1ii=B(_1i7(_1ic)),_1ij=B(_1ib(_1ic,_1ig,B(A3(_nT,_1ii,new T(function(){return B(A3(_1i9,_1ii,_1ig,_1ig));}),_1if))));return new T2(1,_1ij.a,_1ij.b);});return new T2(0,_1if,_1ih);},_1ik=function(_1il){return E(E(_1il).b);},_1im=function(_1in,_1io){var _1ip=E(_1io);if(!_1ip._){return __Z;}else{var _1iq=_1ip.a;return (!B(A1(_1in,_1iq)))?__Z:new T2(1,_1iq,new T(function(){return B(_1im(_1in,_1ip.b));}));}},_1ir=function(_1is,_1it,_1iu,_1iv,_1iw){var _1ix=B(_1ib(_1it,_1iu,_1iv)),_1iy=new T(function(){var _1iz=new T(function(){return B(_1i7(_1it));}),_1iA=new T(function(){return B(A3(_1ik,_1it,new T(function(){return B(A3(_nT,_1iz,_1iv,_1iu));}),new T(function(){return B(A2(_d1,_1iz,_jC));})));});if(!B(A3(_zG,_1is,_1iv,_1iu))){var _1iB=new T(function(){return B(A3(_1i9,_1iz,_1iw,_1iA));});return function(_1iC){return new F(function(){return A3(_zG,_1is,_1iC,_1iB);});};}else{var _1iD=new T(function(){return B(A3(_1i9,_1iz,_1iw,_1iA));});return function(_1iE){return new F(function(){return A3(_zE,_1is,_1iE,_1iD);});};}});return new F(function(){return _1im(_1iy,new T2(1,_1ix.a,_1ix.b));});},_1iF=function(_1iG,_){var _1iH=E(_1iG);if(!_1iH._){return _6;}else{var _1iI=B(A1(_1iH.a,_)),_1iJ=B(_1iF(_1iH.b,_));return new T2(1,_1iI,_1iJ);}},_1iK=function(_1iL,_1iM){return function(_){var _1iN=B(_14b(_)),_1iO=new T(function(){return E(E(_1iN).b);}),_1iP=new T(function(){return E(_1iO)+100;}),_1iQ=new T(function(){return E(E(_1iN).a)/2;}),_1iR=new T(function(){return E(_1iQ)/2;}),_1iS=new T(function(){return E(_1iQ)/5+30;}),_1iT=new T(function(){return E(_1iQ)/5;}),_1iU=function(_){var _1iV=function(_){var _1iW=B(_oG(new T2(0,_1ab,_1iQ),_)),_1iX=B(_oG(new T2(0,_1ab,_1iO),_));return new T2(0,_1iW,_1iX);},_1iY=function(_1iZ){var _1j0=E(_1iZ);return (_1j0==1)?E(new T2(1,_1iV,_6)):new T2(1,_1iV,new T(function(){return B(_1iY(_1j0-1|0));}));},_1j1=B(_1iF(B(_1iY(100)),_)),_1j2=new T(function(){return B(_Yc(_Yi,B(_Yl(_1d6,B(_tH(B(_1hU(_1cZ,B(_1hU(_1de,_1j1)))),10))))));}),_1j3=new T(function(){var _1j4=B(_Za(_1j2,_1iQ,_1iO));return new T2(0,_1j4.a,_1j4.b);}),_1j5=new T(function(){return E(E(_1j3).b);}),_1j6=function(_1j7){var _1j8=E(_1j7);if(!_1j8._){return E(_oN);}else{var _1j9=E(_1j8.a),_1ja=B(_v4(_1j9,_1j5));if(!_1ja._){return E(_oN);}else{var _1jb=new T(function(){return E(E(_1ja.a).b);}),_1jc=new T(function(){return E(E(_1jb).c);}),_1jd=new T(function(){var _1je=B(_uK(_1iR,_1iS,_cm,_1iT,_1jc)),_1jf=function(_1jg){var _1jh=E(_1jg);if(!_1jh._){return E(_oN);}else{var _1ji=E(_1jh.a),_1jj=_1ji.a,_1jk=_1ji.c,_1jl=_1ji.d,_1jm=E(_1ji.b),_1jn=new T(function(){return E(E(_1jj).b);}),_1jo=new T(function(){return E(E(_1jj).a)+E(_1iQ);}),_1jp=new T(function(){return B(_1jf(_1jh.b));}),_1jq=function(_1jr){return E(_1jp);},_1js=new T(function(){var _1jt=new T(function(){var _1ju=new T(function(){var _1jv=function(_1jw){var _1jx=E(_1jk);if(!_1jx._){return new T3(0,_5k,_5f,_7);}else{var _1jy=E(_1jx.c);if(!_1jy._){return new T3(0,_5k,_5f,_7);}else{var _1jz=new T(function(){var _1jA=E(_1je);if(!_1jA._){return E(_1an);}else{var _1jB=_1jA.b,_1jC=E(_1jA.a),_1jD=E(_1jC.b),_1jE=E(_1jy.b),_1jF=E(_1jE.a).a,_1jG=E(_1jE.b).a;if(E(_1jD.a)!=_1jF){var _1jH=function(_1jI){while(1){var _1jJ=E(_1jI);if(!_1jJ._){return E(_1an);}else{var _1jK=_1jJ.b,_1jL=E(_1jJ.a),_1jM=E(_1jL.b);if(E(_1jM.a)!=_1jF){_1jI=_1jK;continue;}else{if(E(_1jM.b)!=_1jG){_1jI=_1jK;continue;}else{return new T5(0,_1jL.a,_1jM,_1jL.c,_1jL.d,_1jL.e);}}}}};return E(B(_1jH(_1jB)).a);}else{if(E(_1jD.b)!=_1jG){var _1jN=function(_1jO){while(1){var _1jP=E(_1jO);if(!_1jP._){return E(_1an);}else{var _1jQ=_1jP.b,_1jR=E(_1jP.a),_1jS=E(_1jR.b);if(E(_1jS.a)!=_1jF){_1jO=_1jQ;continue;}else{if(E(_1jS.b)!=_1jG){_1jO=_1jQ;continue;}else{return new T5(0,_1jR.a,_1jS,_1jR.c,_1jR.d,_1jR.e);}}}}};return E(B(_1jN(_1jB)).a);}else{return E(_1jC.a);}}}}),_1jT=new T(function(){return E(E(_1jz).b);}),_1jU=new T(function(){return E(E(_1jz).a)+E(_1iQ);}),_1jV=new T(function(){return Math.sqrt(Math.pow(E(_1jU)-E(_1jo),2)+Math.pow(E(_1jT)-E(_1jn),2));}),_1jW=new T(function(){return (E(_1jU)-E(_1jo))/E(_1jV);}),_1jX=new T(function(){return (E(_1jT)-E(_1jn))/E(_1jV);});return new F(function(){return _ur(new T2(0,new T1(0,new T(function(){return E(_1jo)+E(_1jW)*E(_1jl);})),new T1(0,new T(function(){return E(_1jn)+E(_1jX)*E(_1jl);}))),new T2(0,new T1(0,new T(function(){return E(_1jU)-E(_1jW)*E(_1jl)/2;})),new T1(0,new T(function(){return E(_1jT)-E(_1jX)*E(_1jl)/2;}))));});}}},_1jY=E(_1jk);if(!_1jY._){var _1jZ=new T(function(){var _1k0=B(_1jv(_));return new T3(0,_1k0.a,_1k0.b,_1k0.c);});return new T3(0,function(_1k1,_){var _1k2=B(A2(E(_1jZ).a,_1k1,_));return _5i;},function(_1k3,_1k4,_){return new F(function(){return A3(E(_1jZ).b,_1k3,_1k4,_);});},new T(function(){return E(E(_1jZ).c);}));}else{var _1k5=E(_1jY.a);if(!_1k5._){var _1k6=new T(function(){var _1k7=B(_1jv(_));return new T3(0,_1k7.a,_1k7.b,_1k7.c);});return new T3(0,function(_1k8,_){var _1k9=B(A2(E(_1k6).a,_1k8,_));return _5i;},function(_1ka,_1kb,_){return new F(function(){return A3(E(_1k6).b,_1ka,_1kb,_);});},new T(function(){return E(E(_1k6).c);}));}else{var _1kc=new T(function(){var _1kd=E(_1je);if(!_1kd._){return E(_1an);}else{var _1ke=_1kd.b,_1kf=E(_1kd.a),_1kg=E(_1kf.b),_1kh=E(_1k5.b),_1ki=E(_1kh.a).a,_1kj=E(_1kh.b).a;if(E(_1kg.a)!=_1ki){var _1kk=function(_1kl){while(1){var _1km=E(_1kl);if(!_1km._){return E(_1an);}else{var _1kn=_1km.b,_1ko=E(_1km.a),_1kp=E(_1ko.b);if(E(_1kp.a)!=_1ki){_1kl=_1kn;continue;}else{if(E(_1kp.b)!=_1kj){_1kl=_1kn;continue;}else{return new T5(0,_1ko.a,_1kp,_1ko.c,_1ko.d,_1ko.e);}}}}};return E(B(_1kk(_1ke)).a);}else{if(E(_1kg.b)!=_1kj){var _1kq=function(_1kr){while(1){var _1ks=E(_1kr);if(!_1ks._){return E(_1an);}else{var _1kt=_1ks.b,_1ku=E(_1ks.a),_1kv=E(_1ku.b);if(E(_1kv.a)!=_1ki){_1kr=_1kt;continue;}else{if(E(_1kv.b)!=_1kj){_1kr=_1kt;continue;}else{return new T5(0,_1ku.a,_1kv,_1ku.c,_1ku.d,_1ku.e);}}}}};return E(B(_1kq(_1ke)).a);}else{return E(_1kf.a);}}}}),_1kw=new T(function(){return E(E(_1kc).b);}),_1kx=new T(function(){return E(E(_1kc).a)+E(_1iQ);}),_1ky=new T(function(){return Math.sqrt(Math.pow(E(_1kx)-E(_1jo),2)+Math.pow(E(_1kw)-E(_1jn),2));}),_1kz=new T(function(){return (E(_1kx)-E(_1jo))/E(_1ky);}),_1kA=new T(function(){return (E(_1kw)-E(_1jn))/E(_1ky);}),_1kB=B(_ur(new T2(0,new T1(0,new T(function(){return E(_1jo)+E(_1kz)*E(_1jl);})),new T1(0,new T(function(){return E(_1jn)+E(_1kA)*E(_1jl);}))),new T2(0,new T1(0,new T(function(){return E(_1kx)-E(_1kz)*E(_1jl)/2;})),new T1(0,new T(function(){return E(_1kw)-E(_1kA)*E(_1jl)/2;}))))),_1kC=new T(function(){var _1kD=B(_1jv(_));return new T3(0,_1kD.a,_1kD.b,_1kD.c);}),_1kE=function(_1kF,_){var _1kG=B(A2(_1kB.a,_1kF,_)),_1kH=B(A2(E(_1kC).a,_1kF,_));return new T(function(){return B(_142(_1kG,_1kH));});};return new T3(0,_1kE,function(_1kI,_1kJ,_){var _1kK=B(A3(_1kB.b,_1kI,_1kJ,_));return new F(function(){return A3(E(_1kC).b,_1kI,_1kJ,_);});},new T(function(){return E(E(_1kC).c);}));}}});return B(_1bl(_1b1,_1aY,_1ju));}),_1kL=new T(function(){var _1kM=E(_1jl),_1kN=_1kM/2,_1kO=new T(function(){return B(A3(_f8,_eY,new T2(1,function(_1kP){return new F(function(){return _fi(0,E(_1jm.a),_1kP);});},new T2(1,function(_1kQ){return new F(function(){return _fi(0,E(_1jm.b),_1kQ);});},_6)),_1aZ));});if(_1kN<=10){var _1kR=B(_vm(_1b5,new T1(0,new T2(1,_eD,_1kO)),_145,_148,new T1(0,new T(function(){if(!E(_1ji.e)){return E(_1jo)-(_1kM+15);}else{return E(_1jo)+_1kM+15;}})),new T1(0,_1jn),new T1(0,new T(function(){if(_1kN>10){return _1kN;}else{return E(_1aj);}}))));return new T3(0,_1kR.a,_1kR.b,_1kR.c);}else{var _1kS=B(_vm(_1b5,new T1(0,new T2(1,_eD,_1kO)),_145,_148,new T1(0,_1jo),new T1(0,_1jn),new T1(0,new T(function(){if(_1kN>10){return _1kN;}else{return E(_1aj);}}))));return new T3(0,_1kS.a,_1kS.b,_1kS.c);}}),_1kT=B(_19a(_1aY,_1kL));if(!_1kT._){return E(_1jt);}else{return new T2(1,_1kT.a,new T2(1,_1kT.b,new T1(0,function(_1kU){return E(_1jt);})));}}),_1kV=B(_1bl(_1b1,_1aY,new T(function(){var _1kW=B(_qZ(new T1(0,_1jo),new T1(0,_1jn),new T1(0,_1jl)));return new T3(0,_1kW.a,_1kW.b,_1kW.c);})));if(!_1kV._){var _1kX=E(_1js);return (_1kX._==0)?E(_1jp):new T2(1,_1kX.a,new T2(1,_1kX.b,new T1(0,_1jq)));}else{return new T2(1,_1kV.a,new T2(1,new T2(1,_1kV.b,new T1(0,function(_1kY){return E(_1js);})),new T1(0,_1jq)));}}};return B(_1jf(_1je));}),_1kZ=new T(function(){var _1l0=E(_1jb),_1l1=new T(function(){var _1l2=new T(function(){var _1l3=new T(function(){var _1l4=new T(function(){return B(_1hU(_5m,B(_1bX(B(_1cS(_1jc))))));}),_1l5=new T(function(){return B(_tR(_1l4,0))-1|0;}),_1l6=function(_1l7,_1l8){var _1l9=E(_1l7);if(!_1l9._){return E(_1ak);}else{var _1la=E(_1l8);if(!_1la._){return E(_1ak);}else{var _1lb=E(_1la.a),_1lc=_1lb.b,_1ld=_1lb.c,_1le=new T(function(){return B(_1l6(_1l9.b,_1la.b));}),_1lf=function(_1lg){var _1lh=E(_1le);return (_1lh._==0)?new T1(0,new T2(1,_1lg,_1lh.a)):new T2(1,_1lh.a,new T2(1,_1lh.b,new T1(0,function(_1li){return new T1(0,new T2(1,_1lg,_1li));})));};if(_1ld>_1j9){return new F(function(){return _1lf(_7);});}else{var _1lj=E(_1l9.a),_1lk=function(_1ll,_1lm){var _1ln=E(_1l5),_1lo=function(_1lp,_1lq){var _1lr=new T(function(){return _1lp<=_1ll;}),_1ls=function(_1lt){var _1lu=function(_1lv){var _1lw=E(_1lv);if(!_1lw._){return E(_oN);}else{var _1lx=E(_1lw.a),_1ly=new T(function(){return B(_1lu(_1lw.b));}),_1lz=function(_1lA){return E(_1ly);},_1lB=function(_1lC,_1lD){var _1lE=(_1lc*_1lc-(_1lc+_1lc)*_1lC+_1ld*_1ld-_1j9*_1j9+_1lC*_1lC)/(_1ld+_1ld-(_1j9+_1j9));if(_1lE<0){return E(_oN);}else{if(_1lE>E(_1iO)){return E(_oN);}else{var _1lF=new T(function(){var _1lG=_1lx+_1lt,_1lH=new T(function(){if(_1lG>_1lp){if(!E(_1lr)){return E(_1lq);}else{return E(_1lm);}}else{if(_1lG>_1ll){return _1lG;}else{return E(_1lm);}}}),_1lI=B(_ur(new T2(0,new T1(0,_1lD),new T1(0,_1lE)),new T2(0,new T1(0,_1lH),new T1(0,new T(function(){var _1lJ=E(_1lH);return (_1lc*_1lc-(_1lc+_1lc)*_1lJ+_1ld*_1ld-_1j9*_1j9+_1lJ*_1lJ)/(_1ld+_1ld-(_1j9+_1j9));})))));return new T3(0,_1lI.a,_1lI.b,_1lI.c);});return new F(function(){return _1bl(_1b1,_1d5,_1lF);});}}};if(_1lx>_1lp){if(!E(_1lr)){var _1lK=B(_1lB(_1lp,_1lq));return (_1lK._==0)?E(_1ly):new T2(1,_1lK.a,new T2(1,_1lK.b,new T1(0,_1lz)));}else{var _1lL=B(_1lB(_1ll,_1lm));return (_1lL._==0)?E(_1ly):new T2(1,_1lL.a,new T2(1,_1lL.b,new T1(0,_1lz)));}}else{if(_1lx>_1ll){var _1lM=B(_1lB(_1lx,_1lx));return (_1lM._==0)?E(_1ly):new T2(1,_1lM.a,new T2(1,_1lM.b,new T1(0,_1lz)));}else{var _1lN=B(_1lB(_1ll,_1lm));return (_1lN._==0)?E(_1ly):new T2(1,_1lN.a,new T2(1,_1lN.b,new T1(0,_1lz)));}}}},_1lO=B(_1lu(B(_1ir(_bP,_a8,_1lm,_1ll+_1lt,_1lq))));if(!_1lO._){return new F(function(){return _1lf(_1lO.a);});}else{return new T2(1,_1lO.a,new T2(1,_1lO.b,new T1(0,_1lf)));}};if((_1lp-_1ll)/15<=20){return new F(function(){return _1ls((_1lp-_1ll)/15);});}else{return new F(function(){return _1ls((_1lp-_1ll)/50);});}};if(_1lj>=_1ln){var _1lP=E(_1iQ);return new F(function(){return _1lo(_1lP,_1lP);});}else{if(_1lj>=_1ln){return E(_1aR);}else{var _1lQ=B(_oZ(_1l4,_1lj+1|0)),_1lR=_1lQ.b,_1lS=_1lQ.c,_1lT=_1ld-_1lS;if(_1lT!=0){if(_1lT<=0){if( -_1lT>=1.0e-7){var _1lU=(_1ld*_1lR+Math.sqrt(((_1lc-_1lR)*(_1lc-_1lR)+_1lT*_1lT)*(_1ld-_1j9)*(_1lS-_1j9))+(_1lc*(_1j9-_1lS)-_1lR*_1j9))/_1lT;return new F(function(){return _1lo(_1lU,_1lU);});}else{var _1lV=(_1lc+_1lR)/2;return new F(function(){return _1lo(_1lV,_1lV);});}}else{if(_1lT>=1.0e-7){var _1lW=(_1ld*_1lR+Math.sqrt(((_1lc-_1lR)*(_1lc-_1lR)+_1lT*_1lT)*(_1ld-_1j9)*(_1lS-_1j9))+(_1lc*(_1j9-_1lS)-_1lR*_1j9))/_1lT;return new F(function(){return _1lo(_1lW,_1lW);});}else{var _1lX=(_1lc+_1lR)/2;return new F(function(){return _1lo(_1lX,_1lX);});}}}else{var _1lY=(_1lc+_1lR)/2;return new F(function(){return _1lo(_1lY,_1lY);});}}}};if(_1lj<=0){return new F(function(){return _1lk(0,0);});}else{var _1lZ=B(_oZ(_1l4,_1lj-1|0)),_1m0=_1lZ.b,_1m1=_1lZ.c,_1m2=_1m1-_1ld;if(_1m2!=0){if(_1m2<=0){if( -_1m2>=1.0e-7){var _1m3=(_1m1*_1lc+Math.sqrt(((_1m0-_1lc)*(_1m0-_1lc)+_1m2*_1m2)*(_1m1-_1j9)*(_1ld-_1j9))+(_1m0*(_1j9-_1ld)-_1lc*_1j9))/_1m2;return new F(function(){return _1lk(_1m3,_1m3);});}else{var _1m4=(_1m0+_1lc)/2;return new F(function(){return _1lk(_1m4,_1m4);});}}else{if(_1m2>=1.0e-7){var _1m5=(_1m1*_1lc+Math.sqrt(((_1m0-_1lc)*(_1m0-_1lc)+_1m2*_1m2)*(_1m1-_1j9)*(_1ld-_1j9))+(_1m0*(_1j9-_1ld)-_1lc*_1j9))/_1m2;return new F(function(){return _1lk(_1m5,_1m5);});}else{var _1m6=(_1m0+_1lc)/2;return new F(function(){return _1lk(_1m6,_1m6);});}}}else{var _1m7=(_1m0+_1lc)/2;return new F(function(){return _1lk(_1m7,_1m7);});}}}}}};return B(_1l6(_1cR,_1l4));});return B(_aY(_7,_1l3));});if(!E(_1l0.a)){return E(_1l2);}else{var _1m8=E(_1l0.d),_1m9=B(_oZ(_1j2,E(_1m8.a))),_1ma=B(_oZ(_1j2,E(_1m8.b))),_1mb=B(_oZ(_1j2,E(_1m8.c))),_1mc=E(_1m9.a),_1md=E(_1m9.b),_1me=E(_1mb.a)-_1mc,_1mf=E(_1mb.b)-_1md,_1mg=E(_1ma.a)-_1mc,_1mh=E(_1ma.b)-_1md,_1mi=_1mg*_1mf-_1mh*_1me+(_1mg*_1mf-_1mh*_1me);if(_1mi>0){var _1mj=new T(function(){var _1mk=_1me*_1me+_1mf*_1mf,_1ml=_1mg*_1mg+_1mh*_1mh,_1mm=new T(function(){return _1mc+(_1mf*_1ml-_1mh*_1mk)/_1mi;}),_1mn=new T(function(){return _1md+(_1mg*_1mk-_1me*_1ml)/_1mi;}),_1mo=B(_qZ(new T1(0,_1mm),new T1(0,_1mn),new T1(0,new T(function(){var _1mp=E(_1mm),_1mq=E(_1mn);return Math.sqrt((_1mp-_1mc)*(_1mp-_1mc)+(_1mq-_1md)*(_1mq-_1md));}))));return new T3(0,_1mo.a,_1mo.b,_1mo.c);}),_1mr=B(_1bl(_1b1,_1c1,_1mj));if(!_1mr._){return E(_1l2);}else{return new T2(1,_1mr.a,new T2(1,_1mr.b,new T1(0,function(_1ms){return E(_1l2);})));}}else{return E(_1l2);}}}),_1mt=B(_1c4(_oN,_1l0.b));if(!_1mt._){return E(_1l1);}else{return new T2(1,_1mt.a,new T2(1,_1mt.b,new T1(0,function(_1mu){return E(_1l1);})));}}),_1mv=B(_1az(_1ad,_1kZ));return (_1mv._==0)?E(_1jd):new T2(1,_1mv.a,new T2(1,_1mv.b,new T1(0,function(_1mw){return E(_1jd);})));}}},_1mx=new T(function(){return B(_1az(_1ad,new T(function(){return B(_1bC(E(_1j3).a));})));}),_1my=function(_){var _1mz=nMV(_1dd),_1mA=_1mz;return new T(function(){var _1mB=new T(function(){return B(_sp(_bc,_1di,_1cY,_1mA,_1iP,_1aM));}),_1mC=new T(function(){return B(_tk(_1mA,_1ab));}),_1mD=function(_1mE){return new F(function(){return _sp(_bc,_1di,_1cY,_1mA,_1iP,function(_1mF){return E(_1mE);});});},_1mG=function(_1mH){return new F(function(){return _1mI(E(_1mH).b);});},_1mJ=function(_1mK){return new F(function(){return A2(_1mC,E(_1mK).b,_1mG);});},_1mL=function(_1mM){return new T1(0,B(_qf(_1mD,E(_1mM).b,_1mJ)));},_1mI=function(_1mN){return new F(function(){return A2(_1mB,_1mN,_1mL);});},_1mO=function(_1mP,_1mQ,_1mR){return new T1(1,new T2(1,new T(function(){return B(A1(_1mR,new T2(0,_7,_1mQ)));}),new T2(1,new T(function(){return B(_1mI(_1mQ));}),_6)));},_1mS=new T(function(){var _1mT=new T(function(){var _1mU=new T(function(){var _1mV=function(_){var _1mW=rMV(_1mA),_1mX=E(_1mW);return (_1mX._==0)?new T1(1,new T(function(){return B(_qv(_1mX.a));})):_2o;},_1mY=new T2(1,new T1(1,_1mV),new T2(1,new T2(1,_1al,new T1(0,_1j6)),new T1(0,function(_1mZ){return E(_1mx);}))),_1n0=B(_1bl(_1b1,_1aY,new T(function(){var _1n1=new T3(0,_1di,_1cY,_1mA),_1n2=B(_ur(new T2(0,_1ac,new T2(2,_1n1,_2E)),new T2(0,_14h,new T2(2,_1n1,_2E))));return new T3(0,_1n2.a,_1n2.b,_1n2.c);})));if(!_1n0._){return E(_1mY);}else{return new T2(1,_1n0.a,new T2(1,_1n0.b,new T1(0,function(_1n3){return E(_1mY);})));}}),_1n4=B(_aY(_7,new T(function(){return B(_1cx(_1cR,_1j2));})));if(!_1n4._){return E(_1mU);}else{return new T2(1,_1n4.a,new T2(1,_1n4.b,new T1(0,function(_1n5){return E(_1mU);})));}}),_1n6=E(_1ai);if(!_1n6._){return E(_1mT);}else{return new T2(1,_1n6.a,new T2(1,_1n6.b,new T1(0,function(_1n7){return E(_1mT);})));}});return B(A(_1fj,[_146,_1ad,_1mS,_1mO,_1iL,_1iM]));});};return new T1(0,_1my);};return new T1(0,_1iU);};},_1n8=function(_1n9,_1na,_1nb){return new F(function(){return A1(_1nb,new T2(0,new T2(0,_1n9,_1n9),_1na));});},_1nc=0,_1nd=function(_1ne,_1nf){var _1ng=E(_1ne);if(!_1ng._){return new F(function(){return A1(_1ng.a,_1nf);});}else{var _1nh=function(_1ni,_1nj){while(1){var _1nk=E(_1ni);if(!_1nk._){var _1nl=B(A1(_1nk.a,_1nf));if(!_1nl._){return new F(function(){return _1nd(_1nj,_1nl.a);});}else{return new T2(1,_1nl.a,new T2(1,_1nl.b,_1nj));}}else{var _1nm=new T2(1,_1nk.b,_1nj);_1ni=_1nk.a;_1nj=_1nm;continue;}}};return new F(function(){return _1nh(_1ng.a,_1ng.b);});}},_1nn=function(_1no,_1np,_1nq){var _1nr=function(_){var _1ns=B(A1(_1no,_));return new T(function(){return B(A1(_1nq,new T2(0,_1ns,_1np)));});};return new T1(0,_1nr);},_1nt=function(_1nu,_1nv,_1nw){var _1nx=E(_1nu);switch(_1nx._){case 0:return new F(function(){return A1(_1nw,new T2(0,_1nx.a,_1nv));});break;case 1:return new F(function(){return _1nn(_1nx.a,_1nv,_1nw);});break;case 2:var _1ny=E(_1nx.a).c,_1nz=function(_1nA){var _1nB=new T(function(){var _1nC=new T(function(){return B(A1(_1nx.b,new T(function(){return B(_qv(_1nA));})));});return B(A1(_1nw,new T2(0,_1nC,_1nv)));});return new T1(0,B(_p6(_1ny,_1nA,function(_1nD){return E(_1nB);})));};return new T1(0,B(_pi(_1ny,_1nz)));default:var _1nE=E(_1nx.a).c,_1nF=function(_1nG){var _1nH=function(_){var _1nI=B(A2(_1nx.b,new T(function(){return B(_qv(_1nG));}),_));return new T(function(){return B(A1(_1nw,new T2(0,_1nI,_1nv)));});};return new T1(0,B(_p6(_1nE,_1nG,function(_1nJ){return E(new T1(0,_1nH));})));};return new T1(0,B(_pi(_1nE,_1nF)));}},_1nK=function(_1nL,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR){while(1){var _1nS=B((function(_1nT,_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ){var _1o0=new T(function(){return 0*E(_1nU)+0*E(_1nV)+E(_1nW);}),_1o1=new T(function(){return 0*E(_1nX)+0*E(_1nY)+E(_1nZ);}),_1o2=E(_1nT);if(!_1o2._){return function(_az,_aA){return new F(function(){return _3Q(_1o2.a,_az,_aA);});};}else{var _1o3=_1o2.b,_1o4=E(_1o2.a);switch(_1o4._){case 0:var _1o5=_1nU,_1o6=_1nV,_1o7=_1nW,_1o8=_1nX,_1o9=_1nY,_1oa=_1nZ;_1nL=B(_1nd(_1o3,_1o4.b));_1nM=_1o5;_1nN=_1o6;_1nO=_1o7;_1nP=_1o8;_1nQ=_1o9;_1nR=_1oa;return __continue;case 1:var _1ob=function(_1oc,_1od){var _1oe=function(_){var _1of=B(A1(_1o4.a,_));return new T(function(){return B(A(_1nK,[B(_1nd(_1o3,_1of)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ,_1oc,_1od]));});};return new T1(0,_1oe);};return E(_1ob);case 2:var _1og=new T(function(){return B(A(_1o4.a,[_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ]));}),_1oh=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.b)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1oi=function(_1oj){var _1ok=new T(function(){return B(A1(_1og,_1oj));}),_1ol=function(_1om){return new F(function(){return A1(_1ok,function(_1on){return new F(function(){return A2(_1oh,E(_1on).b,_1om);});});});};return E(_1ol);};return E(_1oi);case 3:var _1oo=new T(function(){return B(_1nK(_1o4.b,_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1op=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.c)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1oq=function(_1or){var _1os=new T(function(){return B(A1(_1oo,_1or));}),_1ot=function(_1ou){return new F(function(){return A1(_1os,function(_1ov){return new F(function(){return A2(_1op,E(_1ov).b,_1ou);});});});};return E(_1ot);};return E(_1oq);case 4:var _1ow=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.h)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1ox=function(_1oy,_1oz){var _1oA=function(_1oB){return new F(function(){return A2(_1ow,E(_1oB).b,_1oz);});},_1oC=function(_1oD){var _1oE=E(_1oD),_1oF=_1oE.a,_1oG=function(_1oH){var _1oI=E(_1oH),_1oJ=_1oI.a,_1oK=function(_1oL){var _1oM=E(_1oL),_1oN=_1oM.a,_1oO=function(_1oP){var _1oQ=E(_1oP),_1oR=_1oQ.a,_1oS=new T(function(){return E(_1oF)*E(_1nX)+E(_1oR)*E(_1nY);}),_1oT=new T(function(){return E(_1oF)*E(_1nU)+E(_1oR)*E(_1nV);}),_1oU=function(_1oV){var _1oW=E(_1oV),_1oX=_1oW.a,_1oY=new T(function(){return E(_1oJ)*E(_1nX)+E(_1oX)*E(_1nY);}),_1oZ=new T(function(){return E(_1oJ)*E(_1nU)+E(_1oX)*E(_1nV);}),_1p0=function(_1p1){var _1p2=E(_1p1),_1p3=_1p2.a;return new F(function(){return A(_1nK,[_1o4.g,_1oT,_1oZ,new T(function(){return E(_1oN)*E(_1nU)+E(_1p3)*E(_1nV)+E(_1nW);}),_1oS,_1oY,new T(function(){return E(_1oN)*E(_1nX)+E(_1p3)*E(_1nY)+E(_1nZ);}),_1p2.b,_1oA]);});};return new F(function(){return _1nt(_1o4.f,_1oW.b,_1p0);});};return new F(function(){return _1nt(_1o4.e,_1oQ.b,_1oU);});};return new F(function(){return _1nt(_1o4.d,_1oM.b,_1oO);});};return new F(function(){return _1nt(_1o4.c,_1oI.b,_1oK);});};return new F(function(){return _1nt(_1o4.b,_1oE.b,_1oG);});};return new F(function(){return _1nt(_1o4.a,_1oy,_1oC);});};return E(_1ox);case 5:var _1p4=E(_1o4.a),_1p5=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.c)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1p6=new T(function(){return 0*E(_1nX)+E(_1nY);}),_1p7=new T(function(){return E(_1nX)+0*E(_1nY);}),_1p8=new T(function(){return 0*E(_1nU)+E(_1nV);}),_1p9=new T(function(){return E(_1nU)+0*E(_1nV);}),_1pa=function(_1pb,_1pc){var _1pd=function(_1pe){return new F(function(){return A2(_1p5,E(_1pe).b,_1pc);});},_1pf=function(_1pg){var _1ph=E(_1pg),_1pi=_1ph.a,_1pj=function(_1pk){var _1pl=E(_1pk),_1pm=_1pl.a;return new F(function(){return A(_1nK,[_1o4.b,_1p9,_1p8,new T(function(){return E(_1pi)*E(_1nU)+E(_1pm)*E(_1nV)+E(_1nW);}),_1p7,_1p6,new T(function(){return E(_1pi)*E(_1nX)+E(_1pm)*E(_1nY)+E(_1nZ);}),_1pl.b,_1pd]);});};return new F(function(){return _1nt(_1p4.b,_1ph.b,_1pj);});};return new F(function(){return _1nt(_1p4.a,_1pb,_1pf);});};return E(_1pa);case 6:var _1pn=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.c)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1po=function(_1pp,_1pq){var _1pr=function(_1ps){return new F(function(){return A2(_1pn,E(_1ps).b,_1pq);});},_1pt=function(_1pu){var _1pv=E(_1pu),_1pw=_1pv.a,_1px=new T(function(){return Math.cos(E(_1pw));}),_1py=new T(function(){return Math.sin(E(_1pw));}),_1pz=new T(function(){return  -E(_1py);});return new F(function(){return A(_1nK,[_1o4.b,new T(function(){return E(_1px)*E(_1nU)+E(_1py)*E(_1nV);}),new T(function(){return E(_1pz)*E(_1nU)+E(_1px)*E(_1nV);}),_1o0,new T(function(){return E(_1px)*E(_1nX)+E(_1py)*E(_1nY);}),new T(function(){return E(_1pz)*E(_1nX)+E(_1px)*E(_1nY);}),_1o1,_1pv.b,_1pr]);});};return new F(function(){return _1nt(_1o4.a,_1pp,_1pt);});};return E(_1po);case 7:var _1pA=E(_1o4.a),_1pB=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.c)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1pC=function(_1pD,_1pE){var _1pF=function(_1pG){return new F(function(){return A2(_1pB,E(_1pG).b,_1pE);});},_1pH=function(_1pI){var _1pJ=E(_1pI),_1pK=_1pJ.a,_1pL=new T(function(){return E(_1pK)*E(_1nX)+0*E(_1nY);}),_1pM=new T(function(){return E(_1pK)*E(_1nU)+0*E(_1nV);}),_1pN=function(_1pO){var _1pP=E(_1pO),_1pQ=_1pP.a;return new F(function(){return A(_1nK,[_1o4.b,_1pM,new T(function(){return 0*E(_1nU)+E(_1pQ)*E(_1nV);}),_1o0,_1pL,new T(function(){return 0*E(_1nX)+E(_1pQ)*E(_1nY);}),_1o1,_1pP.b,_1pF]);});};return new F(function(){return _1nt(_1pA.b,_1pJ.b,_1pN);});};return new F(function(){return _1nt(_1pA.a,_1pD,_1pH);});};return E(_1pC);default:var _1pR=new T(function(){return B(_1nK(_1o4.b,_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1pS=new T(function(){return B(_1nK(B(_1nd(_1o3,_1o4.c)),_1nU,_1nV,_1nW,_1nX,_1nY,_1nZ));}),_1pT=function(_1pU){var _1pV=new T(function(){return B(A1(_1pR,_1pU));}),_1pW=function(_1pX){return new F(function(){return A1(_1pV,function(_1pY){return new F(function(){return A2(_1pS,E(_1pY).b,_1pX);});});});};return E(_1pW);};return E(_1pT);}}})(_1nL,_1nM,_1nN,_1nO,_1nP,_1nQ,_1nR));if(_1nS!=__continue){return _1nS;}}},_1pZ=new T(function(){return eval("(function(e){e.width = e.width;})");}),_1q0=1,_1q1=new T1(1,_6),_1q2=new T(function(){return eval("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");}),_1q3=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_1q4=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_1q5=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_1q6=function(_1q7,_1q8,_){while(1){var _1q9=B((function(_1qa,_1qb,_){var _1qc=E(_1qa);if(!_1qc._){return _1qc.a;}else{var _1qd=_1qc.b,_1qe=E(_1qc.a);switch(_1qe._){case 0:var _1qf=B(A2(_1qe.a,_1qb,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qe.b));_1q8=_1qg;return __continue;case 1:var _1qh=B(A1(_1qe.a,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qh));_1q8=_1qg;return __continue;case 2:var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1qe.b));_1q8=_1qg;return __continue;case 3:var _1qi=B(_1q6(_1qe.b,_1qe.a,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qe.c));_1q8=_1qg;return __continue;case 4:var _1qj=_1qe.h,_1qk=function(_1ql,_){var _1qm=function(_1qn,_){var _1qo=function(_1qp,_){var _1qq=function(_1qr,_){var _1qs=function(_1qt,_){return new F(function(){return _1b7(_1qe.f,function(_1qu,_){var _1qv=E(_1qb),_1qw=__app1(E(_1ay),_1qv),_1qx=__apply(E(_1q2),new T2(1,E(_1qu),new T2(1,E(_1qt),new T2(1,E(_1qr),new T2(1,E(_1qp),new T2(1,E(_1qn),new T2(1,E(_1ql),new T2(1,_1qv,_6)))))))),_1qy=B(_1q6(_1qe.g,_1qv,_)),_1qz=__app1(E(_1ao),_1qv);return new F(function(){return _qV(_);});},_);});};return new F(function(){return _1b7(_1qe.e,_1qs,_);});};return new F(function(){return _1b7(_1qe.d,_1qq,_);});};return new F(function(){return _1b7(_1qe.c,_1qo,_);});};return new F(function(){return _1b7(_1qe.b,_1qm,_);});},_1qA=E(_1qe.a);switch(_1qA._){case 0:var _1qB=B(_1qk(_1qA.a,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qj));_1q8=_1qg;return __continue;case 1:var _1qC=B(A1(_1qA.a,_)),_1qD=B(_1qk(_1qC,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qj));_1q8=_1qg;return __continue;case 2:var _1qE=rMV(E(E(_1qA.a).c)),_1qF=E(_1qE);if(!_1qF._){var _1qG=new T(function(){return B(A1(_1qA.b,new T(function(){return B(_qv(_1qF.a));})));},1),_1qH=B(_1qk(_1qG,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qj));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1qj));_1q8=_1qg;return __continue;}break;default:var _1qI=rMV(E(E(_1qA.a).c)),_1qJ=E(_1qI);if(!_1qJ._){var _1qK=B(A2(_1qA.b,E(_1qJ.a).a,_)),_1qL=B(_1qk(_1qK,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qj));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1qj));_1q8=_1qg;return __continue;}}break;case 5:var _1qM=_1qe.c,_1qN=E(_1qe.a),_1qO=function(_1qP,_){return new F(function(){return _1b7(_1qN.b,function(_1qQ,_){var _1qR=E(_1qb),_1qS=__app1(E(_1ay),_1qR),_1qT=__app3(E(_1q3),_1qR,E(_1qP),E(_1qQ)),_1qU=B(_1q6(_1qe.b,_1qR,_)),_1qV=__app1(E(_1ao),_1qR);return new F(function(){return _qV(_);});},_);});},_1qW=E(_1qN.a);switch(_1qW._){case 0:var _1qX=B(_1qO(_1qW.a,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qM));_1q8=_1qg;return __continue;case 1:var _1qY=B(A1(_1qW.a,_)),_1qZ=B(_1qO(_1qY,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qM));_1q8=_1qg;return __continue;case 2:var _1r0=rMV(E(E(_1qW.a).c)),_1r1=E(_1r0);if(!_1r1._){var _1r2=new T(function(){return B(A1(_1qW.b,new T(function(){return B(_qv(_1r1.a));})));},1),_1r3=B(_1qO(_1r2,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qM));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1qM));_1q8=_1qg;return __continue;}break;default:var _1r4=rMV(E(E(_1qW.a).c)),_1r5=E(_1r4);if(!_1r5._){var _1r6=B(A2(_1qW.b,E(_1r5.a).a,_)),_1r7=B(_1qO(_1r6,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qM));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1qM));_1q8=_1qg;return __continue;}}break;case 6:var _1r8=_1qe.c,_1r9=function(_1ra,_){var _1rb=E(_1qb),_1rc=__app1(E(_1ay),_1rb),_1rd=__app2(E(_1q4),_1rb,E(_1ra)),_1re=B(_1q6(_1qe.b,_1rb,_)),_1rf=__app1(E(_1ao),_1rb);return new F(function(){return _qV(_);});},_1rg=E(_1qe.a);switch(_1rg._){case 0:var _1rh=B(_1r9(_1rg.a,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1r8));_1q8=_1qg;return __continue;case 1:var _1ri=B(A1(_1rg.a,_)),_1rj=B(_1r9(_1ri,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1r8));_1q8=_1qg;return __continue;case 2:var _1rk=rMV(E(E(_1rg.a).c)),_1rl=E(_1rk);if(!_1rl._){var _1rm=new T(function(){return B(A1(_1rg.b,new T(function(){return B(_qv(_1rl.a));})));},1),_1rn=B(_1r9(_1rm,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1r8));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1r8));_1q8=_1qg;return __continue;}break;default:var _1ro=rMV(E(E(_1rg.a).c)),_1rp=E(_1ro);if(!_1rp._){var _1rq=B(A2(_1rg.b,E(_1rp.a).a,_)),_1rr=B(_1r9(_1rq,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1r8));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1r8));_1q8=_1qg;return __continue;}}break;case 7:var _1rs=_1qe.c,_1rt=E(_1qe.a),_1ru=function(_1rv,_){return new F(function(){return _1b7(_1rt.b,function(_1rw,_){var _1rx=E(_1qb),_1ry=__app1(E(_1ay),_1rx),_1rz=__app3(E(_1q5),_1rx,E(_1rv),E(_1rw)),_1rA=B(_1q6(_1qe.b,_1rx,_)),_1rB=__app1(E(_1ao),_1rx);return new F(function(){return _qV(_);});},_);});},_1rC=E(_1rt.a);switch(_1rC._){case 0:var _1rD=B(_1ru(_1rC.a,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1rs));_1q8=_1qg;return __continue;case 1:var _1rE=B(A1(_1rC.a,_)),_1rF=B(_1ru(_1rE,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1rs));_1q8=_1qg;return __continue;case 2:var _1rG=rMV(E(E(_1rC.a).c)),_1rH=E(_1rG);if(!_1rH._){var _1rI=new T(function(){return B(A1(_1rC.b,new T(function(){return B(_qv(_1rH.a));})));},1),_1rJ=B(_1ru(_1rI,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1rs));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1rs));_1q8=_1qg;return __continue;}break;default:var _1rK=rMV(E(E(_1rC.a).c)),_1rL=E(_1rK);if(!_1rL._){var _1rM=B(A2(_1rC.b,E(_1rL.a).a,_)),_1rN=B(_1ru(_1rM,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1rs));_1q8=_1qg;return __continue;}else{var _1qg=_1qb;_1q7=B(_1nd(_1qd,_1rs));_1q8=_1qg;return __continue;}}break;default:var _1rO=B(_1q6(_1qe.a,_1qb,_)),_1qg=_1qb;_1q7=B(_1nd(_1qd,_1qe.c));_1q8=_1qg;return __continue;}}})(_1q7,_1q8,_));if(_1q9!=__continue){return _1q9;}}},_1rP=function(_1rQ){return E(E(_1rQ).b);},_1rR=__Z,_1rS=function(_1rT,_1rU,_1rV,_1rW){var _1rX=E(_1rW);switch(_1rX._){case 0:return new T3(2,_1rU,_1rV,_1rR);case 1:return new T3(2,_1rU,_1rV,_1rX.a);default:var _1rY=_1rX.a,_1rZ=_1rX.b,_1s0=_1rX.c;return new T1(1,new T(function(){if(!B(A2(_1rT,_1rU,_1rY))){return B(_1rS(_1rT,_1rY,new T3(0,_1rU,_1rV,_1rZ),_1s0));}else{return B(_1rS(_1rT,_1rU,new T3(0,_1rY,_1rZ,_1rV),_1s0));}}));}},_1s1=0,_1s2=function(_1s3,_1s4,_1s5){return new F(function(){return A1(_1s5,new T2(0,new T2(0,new T(function(){return E(_1s3).b;}),_1s3),_1s4));});},_1s6=function(_1s7,_1s8,_1s9){var _1sa=function(_1sb){var _1sc=E(_1sb),_1sd=_1sc.b,_1se=new T(function(){return E(_1sc.a)+E(_1s7)|0;}),_1sf=function(_){var _1sg=nMV(_qe),_1sh=_1sg;return new T(function(){var _1si=function(_1sj){var _1sk=new T(function(){return B(A1(_1s9,new T2(0,_7,E(_1sj).b)));});return new T1(0,B(_pi(_1sh,function(_1sl){return E(_1sk);})));},_1sm=new T2(0,_1se,_1sh),_1sn=function(_1so){var _1sp=new T(function(){var _1sq=E(_1so),_1sr=E(_1sq.c);if(!_1sr._){var _1ss=E(new T3(1,1,_1sm,E(_1rR)));}else{var _1st=_1sr.a,_1su=_1sr.c,_1sv=E(_1sr.b),_1sw=E(_1se),_1sx=E(_1sv.a);if(_1sw>=_1sx){if(_1sw!=_1sx){var _1sy=new T3(1,_1st+1|0,_1sv,E(B(_1rS(function(_1sz,_1sA){var _1sB=E(E(_1sz).a),_1sC=E(E(_1sA).a);return (_1sB>=_1sC)?_1sB==_1sC:true;},_1sm,_1s1,_1su))));}else{var _1sy=new T3(1,_1st+1|0,_1sm,E(B(_1rS(function(_1sD,_1sE){var _1sF=E(E(_1sD).a),_1sG=E(E(_1sE).a);return (_1sF>=_1sG)?_1sF==_1sG:true;},_1sv,_1s1,_1su))));}var _1sH=_1sy;}else{var _1sH=new T3(1,_1st+1|0,_1sm,E(B(_1rS(function(_1sI,_1sJ){var _1sK=E(E(_1sI).a),_1sL=E(E(_1sJ).a);return (_1sK>=_1sL)?_1sK==_1sL:true;},_1sv,_1s1,_1su))));}var _1ss=_1sH;}return new T4(0,E(_1sq.a),_1sq.b,E(_1ss),E(_1sq.d));});return function(_1sM,_1sN){return new F(function(){return A1(_1sN,new T2(0,new T2(0,_7,_1sp),_1sM));});};};return B(A(_rS,[_4l,_1sd,_1sn,_1sd,_1si]));});};return new T1(0,_1sf);};return new F(function(){return A(_rS,[_4l,_1s8,_1s2,_1s8,_1sa]);});},_1sO=function(_1sP,_1sQ,_1sR){var _1sS=function(_1sT,_){var _1sU=E(_1sP),_1sV=__app1(E(_1pZ),_1sU.b);return new F(function(){return _1q6(B(_1rP(_1sT)),_1sU.a,_);});},_1sW=function(_1sX){var _1sY=E(_1sX),_1sZ=function(_){var _1t0=nMV(new T2(0,_1sY.a,_6));return new T(function(){var _1t1=new T(function(){return B(_rS(_4l,_1t0,_1n8));}),_1t2=function(_1t3){return new F(function(){return _1t4(E(_1t3).b);});},_1t5=function(_1t6){return new F(function(){return _1s6(_1q0,E(_1t6).b,_1t2);});},_1t7=function(_1t8){var _1t9=E(_1t8);return new F(function(){return A(_1nK,[B(_1rP(_1t9.a)),_1af,_1nc,_1nc,_1nc,_1af,_1nc,_1t9.b,_1t5]);});},_1t4=function(_1ta){return new F(function(){return A2(_1t1,_1ta,_1t7);});},_1tb=function(_1tc){var _1td=E(_1tc).b,_1te=function(_){var _1tf=nMV(_1q1);return new T1(1,new T2(1,new T(function(){return B(A1(_1sR,new T2(0,_7,_1td)));}),new T2(1,new T(function(){return B(_1t4(_1td));}),_6)));};return new T1(0,_1te);};return new T1(0,B(_4t(_1t0,_1sS,_1sY.b,_1tb)));});};return new T1(0,_1sZ);};return new F(function(){return _1iK(_1sQ,_1sW);});},_1tg="deltaZ",_1th="deltaY",_1ti="deltaX",_1tj=new T(function(){return B(unCStr(")"));}),_1tk=new T(function(){return B(_fi(0,2,_1tj));}),_1tl=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_1tk));}),_1tm=function(_1tn){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_fi(0,_1tn,_1tl));}))));});},_1to=function(_1tp,_){return new T(function(){var _1tq=Number(E(_1tp)),_1tr=jsTrunc(_1tq);if(_1tr<0){return B(_1tm(_1tr));}else{if(_1tr>2){return B(_1tm(_1tr));}else{return _1tr;}}});},_1ts=0,_1tt=new T3(0,_1ts,_1ts,_1ts),_1tu="button",_1tv=new T(function(){return eval("jsGetMouseCoords");}),_1tw=function(_1tx,_){var _1ty=E(_1tx);if(!_1ty._){return _6;}else{var _1tz=B(_1tw(_1ty.b,_));return new T2(1,new T(function(){var _1tA=Number(E(_1ty.a));return jsTrunc(_1tA);}),_1tz);}},_1tB=function(_1tC,_){var _1tD=__arr2lst(0,_1tC);return new F(function(){return _1tw(_1tD,_);});},_1tE=function(_1tF,_){return new F(function(){return _1tB(E(_1tF),_);});},_1tG=function(_1tH,_){return new T(function(){var _1tI=Number(E(_1tH));return jsTrunc(_1tI);});},_1tJ=new T2(0,_1tG,_1tE),_1tK=function(_1tL,_){var _1tM=E(_1tL);if(!_1tM._){return _6;}else{var _1tN=B(_1tK(_1tM.b,_));return new T2(1,_1tM.a,_1tN);}},_1tO=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_1tP=new T6(0,_2o,_2p,_6,_1tO,_2o,_2o),_1tQ=new T(function(){return B(_1R(_1tP));}),_1tR=function(_){return new F(function(){return die(_1tQ);});},_1tS=function(_1tT){return E(E(_1tT).a);},_1tU=function(_1tV,_1tW,_1tX,_){var _1tY=__arr2lst(0,_1tX),_1tZ=B(_1tK(_1tY,_)),_1u0=E(_1tZ);if(!_1u0._){return new F(function(){return _1tR(_);});}else{var _1u1=E(_1u0.b);if(!_1u1._){return new F(function(){return _1tR(_);});}else{if(!E(_1u1.b)._){var _1u2=B(A3(_1tS,_1tV,_1u0.a,_)),_1u3=B(A3(_1tS,_1tW,_1u1.a,_));return new T2(0,_1u2,_1u3);}else{return new F(function(){return _1tR(_);});}}}},_1u4=function(_1u5,_1u6,_){if(E(_1u5)==7){var _1u7=__app1(E(_1tv),_1u6),_1u8=B(_1tU(_1tJ,_1tJ,_1u7,_)),_1u9=__get(_1u6,E(_1ti)),_1ua=__get(_1u6,E(_1th)),_1ub=__get(_1u6,E(_1tg));return new T(function(){return new T3(0,E(_1u8),E(_2o),E(new T3(0,_1u9,_1ua,_1ub)));});}else{var _1uc=__app1(E(_1tv),_1u6),_1ud=B(_1tU(_1tJ,_1tJ,_1uc,_)),_1ue=__get(_1u6,E(_1tu)),_1uf=__eq(_1ue,E(_4r));if(!E(_1uf)){var _1ug=B(_1to(_1ue,_));return new T(function(){return new T3(0,E(_1ud),E(new T1(1,_1ug)),E(_1tt));});}else{return new T(function(){return new T3(0,E(_1ud),E(_2o),E(_1tt));});}}},_1uh=function(_1ui,_1uj,_){return new F(function(){return _1u4(_1ui,E(_1uj),_);});},_1uk="mouseout",_1ul="mouseover",_1um="mousemove",_1un="mouseup",_1uo="mousedown",_1up="dblclick",_1uq="click",_1ur="wheel",_1us=function(_1ut){switch(E(_1ut)){case 0:return E(_1uq);case 1:return E(_1up);case 2:return E(_1uo);case 3:return E(_1un);case 4:return E(_1um);case 5:return E(_1ul);case 6:return E(_1uk);default:return E(_1ur);}},_1uu=new T2(0,_1us,_1uh),_1uv=function(_1uw,_){return new T1(1,_1uw);},_1ux=new T2(0,_2E,_1uv),_1uy=function(_1uz,_1uA,_1uB){var _1uC=function(_1uD,_){return new F(function(){return _e(new T(function(){return B(A3(_1uz,_1uD,_1uA,_2H));}),_6,_);});};return new F(function(){return A1(_1uB,new T2(0,_1uC,_1uA));});},_1uE=new T2(0,_4f,_1nn),_1uF=new T2(0,_1uE,_1uy),_1uG=function(_1uH,_1uI,_1uJ){return new F(function(){return A1(_1uJ,new T2(0,new T2(0,new T(function(){return E(E(_1uH).a);}),_1uH),_1uI));});},_1uK=16,_1uL=function(_1uM,_1uN,_1uO){var _1uP=E(_1uM);if(!_1uP._){return new F(function(){return A1(_1uO,new T2(0,_6,_1uN));});}else{var _1uQ=function(_1uR){var _1uS=E(_1uR);return new F(function(){return _1uL(_1uP.b,_1uS.b,function(_1uT){var _1uU=E(_1uT);return new F(function(){return A1(_1uO,new T2(0,new T2(1,_1uS.a,_1uU.a),_1uU.b));});});});};return new F(function(){return A2(E(_1uP.a).a,_1uN,_1uQ);});}},_1uV=function(_1uW,_1uX,_1uY){var _1uZ=E(_1uW);if(!_1uZ._){return new F(function(){return A1(_1uY,new T2(0,_6,_1uX));});}else{var _1v0=E(_1uZ.a),_1v1=function(_1v2){var _1v3=E(_1v2),_1v4=function(_1v5){var _1v6=E(_1v5),_1v7=_1v6.a;return new F(function(){return A1(_1uY,new T2(0,new T(function(){if(!E(_1v3.a)){return E(_1v7);}else{return new T2(1,_1v0,_1v7);}}),_1v6.b));});};return new F(function(){return _1uV(_1uZ.b,_1v3.b,_1v4);});};return new F(function(){return A2(_1v0.b,_1uX,_1v1);});}},_1v8=function(_1v9,_1va){var _1vb=E(_1va);switch(_1vb._){case 0:return __Z;case 1:var _1vc=B(_1v8(_1v9,_1vb.a));if(!_1vc._){return __Z;}else{var _1vd=E(_1vc.b);return new T3(1,_1vc.a,_1vd.c,new T3(2,_1vd.a,_1vd.b,_1vc.c));}break;default:var _1ve=_1vb.a,_1vf=_1vb.b,_1vg=_1vb.c,_1vh=B(_1v8(_1v9,_1vg));if(!_1vh._){return new T3(1,_1ve,_1vf,new T1(1,_1vg));}else{var _1vi=_1vh.a,_1vj=_1vh.c;if(!B(A2(_1v9,_1ve,_1vi))){var _1vk=E(_1vh.b),_1vl=_1vk.a,_1vm=_1vk.b;return new T3(1,_1vi,_1vk.c,new T1(1,new T(function(){if(!B(A2(_1v9,_1ve,_1vl))){return B(_1rS(_1v9,_1vl,new T3(0,_1ve,_1vf,_1vm),_1vj));}else{return B(_1rS(_1v9,_1ve,new T3(0,_1vl,_1vm,_1vf),_1vj));}})));}else{return new T3(1,_1ve,_1vf,new T1(1,_1vg));}}}},_1vn=function(_1vo){var _1vp=new T(function(){var _1vq=E(_1vo),_1vr=E(_1vq.c);if(!_1vr._){var _1vs=__Z;}else{var _1vt=B(_1v8(function(_1vu,_1vv){var _1vw=E(E(_1vu).a),_1vx=E(E(_1vv).a);return (_1vw>=_1vx)?_1vw==_1vx:true;},_1vr.c));if(!_1vt._){var _1vy=__Z;}else{var _1vy=new T3(1,_1vr.a-1|0,_1vt.a,E(_1vt.c));}var _1vs=_1vy;}return new T4(0,E(_1vq.a),_1vq.b,E(_1vs),E(_1vq.d));});return function(_1vz,_1vA){return new F(function(){return A1(_1vA,new T2(0,new T2(0,_7,_1vp),_1vz));});};},_1vB=function(_1vC,_1vD,_1vE){return new F(function(){return A1(_1vE,new T2(0,new T2(0,new T(function(){var _1vF=E(E(_1vC).c);if(!_1vF._){return __Z;}else{return new T1(1,_1vF.b);}}),_1vC),_1vD));});},_1vG=function(_1vH,_1vI,_1vJ){return new F(function(){return A1(_1vJ,new T2(0,new T2(0,_7,new T(function(){var _1vK=E(_1vH);return new T4(0,E(_1vK.a),_1vK.b+1|0,E(_1vK.c),E(_1vK.d));})),_1vI));});},_1vL=function(_1vM,_1vN){return new T1(0,B(_1vO(_1vM)));},_1vP=function(_1vQ){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1vQ));}))));});},_1vR=new T(function(){return B(_1vP("w_sKgA ((), MVar WorldState) -> Action"));}),_1vS=function(_1vT){return new F(function(){return _1vL(E(_1vT).b,_1vR);});},_1vU=function(_1vV){var _1vW=E(_1vV).b;return new F(function(){return A(_rS,[_4l,_1vW,_1vG,_1vW,_1vS]);});},_1vX=function(_1vY,_1vZ){var _1w0=new T(function(){return B(A2(_b1,_1vY,_7));}),_1w1=new T(function(){return B(_1vX(_1vY,_1vZ));});return new F(function(){return A3(_ap,_1vY,_1vZ,function(_1w2){return (!E(_1w2))?E(_1w0):E(_1w1);});});},_1w3=function(_1w4){var _1w5=E(_1w4),_1w6=function(_1w7,_1w8){var _1w9=function(_1wa){return new F(function(){return A1(_1w8,new T2(0,_cm,E(_1wa).b));});},_1wb=function(_1wc){var _1wd=E(_1wc),_1we=_1wd.b,_1wf=E(_1wd.a);if(!_1wf._){return new F(function(){return A1(_1w8,new T2(0,_5i,_1we));});}else{var _1wg=E(_1wf.a);if(E(_1wg.a)<=E(_1w5.a)){var _1wh=new T(function(){return B(A(_rS,[_4l,_1we,_1vn,_1we,_1w9]));});return new T1(0,B(_p6(_1wg.b,_7,function(_1wi){return E(_1wh);})));}else{return new F(function(){return A1(_1w8,new T2(0,_5i,_1we));});}}};return new F(function(){return A(_rS,[_4l,_1w7,_1vB,_1w7,_1wb]);});};return new F(function(){return A(_1vX,[_4f,_1w6,_1w5.b,_1vU]);});},_1wj=function(_1wk){var _1wl=E(_1wk).b;return new F(function(){return A(_rS,[_4l,_1wl,_1s2,_1wl,_1w3]);});},_1wm=function(_1wn){var _1wo=E(_1wn),_1wp=_1wo.b,_1wq=function(_1wr,_1ws,_1wt){return new F(function(){return A1(_1wt,new T2(0,new T2(0,_7,new T(function(){var _1wu=E(_1wr);return new T4(0,E(_1wo.a),_1wu.b,E(_1wu.c),E(_1wu.d));})),_1ws));});};return new F(function(){return A(_rS,[_4l,_1wp,_1wq,_1wp,_1wj]);});},_1wv=function(_1ww){var _1wx=E(_1ww),_1wy=_1wx.a;return new F(function(){return _1uL(_1wy,_1wx.b,function(_1wz){return new F(function(){return _1uV(_1wy,E(_1wz).b,_1wm);});});});},_1vO=function(_1wA){var _1wB=new T(function(){return B(A(_rS,[_4l,_1wA,_1uG,_1wA,_1wv]));});return new F(function(){return _q5(_1uK,function(_1wC){return E(_1wB);});});},_1wD=2,_1wE=4,_1wF=3,_1wG=function(_1wH,_1wI,_1wJ){return new F(function(){return A1(_1wJ,new T2(0,new T2(0,new T(function(){return E(E(E(_1wH).d).b);}),_1wH),_1wI));});},_1wK=new T(function(){return eval("document");}),_1wL=new T1(0,_5i),_1wM=new T1(0,_cm),_1wN=new T1(1,_6),_1wO=__Z,_1wP=new T0(2),_1wQ=new T2(0,_qd,_1wP),_1wR=new T4(0,E(_6),0,E(_1wO),E(_1wQ)),_1wS=new T2(0,_1wR,_6),_1wT=function(_1wU){return E(E(_1wU).a);},_1wV=function(_1wW){return E(E(_1wW).b);},_1wX=function(_1wY){return E(E(_1wY).a);},_1wZ=function(_){return new F(function(){return nMV(_2o);});},_1x0=new T(function(){return B(_4n(_1wZ));}),_1x1=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1x2=function(_1x3,_1x4,_1x5,_1x6,_1x7,_1x8){var _1x9=B(_pw(_1x3)),_1xa=B(_py(_1x9)),_1xb=new T(function(){return B(_pC(_1x9));}),_1xc=new T(function(){return B(_b1(_1xa));}),_1xd=new T(function(){return B(A2(_1wT,_1x4,_1x6));}),_1xe=new T(function(){return B(A2(_1wX,_1x5,_1x7));}),_1xf=function(_1xg){return new F(function(){return A1(_1xc,new T3(0,_1xe,_1xd,_1xg));});},_1xh=function(_1xi){var _1xj=new T(function(){var _1xk=new T(function(){var _1xl=__createJSFunc(2,function(_1xm,_){var _1xn=B(A2(E(_1xi),_1xm,_));return _4r;}),_1xo=_1xl;return function(_){return new F(function(){return __app3(E(_1x1),E(_1xd),E(_1xe),_1xo);});};});return B(A1(_1xb,_1xk));});return new F(function(){return A3(_ap,_1xa,_1xj,_1xf);});},_1xp=new T(function(){var _1xq=new T(function(){return B(_pC(_1x9));}),_1xr=function(_1xs){var _1xt=new T(function(){return B(A1(_1xq,function(_){var _=wMV(E(_1x0),new T1(1,_1xs));return new F(function(){return A(_1wV,[_1x5,_1x7,_1xs,_]);});}));});return new F(function(){return A3(_ap,_1xa,_1xt,_1x8);});};return B(A2(_pE,_1x3,_1xr));});return new F(function(){return A3(_ap,_1xa,_1xp,_1xh);});},_1xu=function(_1xv,_1xw){return new F(function(){return A1(_1xw,new T2(0,_7,_1xv));});},_1xx=function(_1xy,_1xz){return function(_){var _1xA=nMV(_1wS),_1xB=_1xA,_1xC=function(_1xD){return new F(function(){return A1(_1xz,E(_1xD).a);});},_1xE=function(_1xF){return new F(function(){return A2(_1xy,E(_1xF).b,_1xC);});},_1xG=function(_){var _1xH=nMV(_1wN),_1xI=_1xH,_1xJ=new T(function(){var _1xK=function(_1xL){return new F(function(){return _1xM(E(_1xL).b);});},_1xM=function(_1xN){var _1xO=function(_1xP){var _1xQ=function(_1xR){var _1xS=E(_1xR),_1xT=_1xS.b,_1xU=E(_1xP),_1xV=function(_1xW,_1xX,_1xY){var _1xZ=function(_1y0,_1y1){while(1){var _1y2=B((function(_1y3,_1y4){var _1y5=E(_1y4);switch(_1y5._){case 0:_1y0=new T(function(){return B(_1xZ(_1y3,_1y5.d));});_1y1=_1y5.c;return __continue;case 1:var _1y6=new T(function(){return B(_1dj(_4l,_1y5.b,_1xW));}),_1y7=function(_1y8){var _1y9=new T(function(){return B(A1(_1y6,_1y8));}),_1ya=function(_1yb){return new F(function(){return A1(_1y9,function(_1yc){return new F(function(){return A2(_1y3,E(_1yc).b,_1yb);});});});};return E(_1ya);};return E(_1y7);default:return E(_1y3);}})(_1y0,_1y1));if(_1y2!=__continue){return _1y2;}}},_1yd=E(_1xS.a);if(!_1yd._){var _1ye=_1yd.c,_1yf=_1yd.d;if(_1yd.b>=0){return new F(function(){return A(_1xZ,[new T(function(){return B(_1xZ(_1xu,_1yf));}),_1ye,_1xX,_1xY]);});}else{return new F(function(){return A(_1xZ,[new T(function(){return B(_1xZ(_1xu,_1ye));}),_1yf,_1xX,_1xY]);});}}else{return new F(function(){return A(_1xZ,[_1xu,_1yd,_1xX,_1xY]);});}};switch(E(_1xU.a)){case 2:return new F(function(){return _1xV(_1wM,_1xT,_1xK);});break;case 3:return new F(function(){return _1xV(_1wL,_1xT,_1xK);});break;case 4:var _1yg=new T(function(){return E(E(_1xU.b).a);});return new F(function(){return _1xV(new T1(1,new T2(0,new T(function(){return E(E(_1yg).a);}),new T(function(){return E(E(_1yg).b);}))),_1xT,_1xK);});break;default:return new F(function(){return _1xM(_1xT);});}};return new F(function(){return A(_rS,[_4l,_1xN,_1wG,_1xN,_1xQ]);});};return new T1(0,B(_pi(_1xI,_1xO)));};return B(_1xM(_1xB));}),_1yh=new T(function(){var _1yi=new T(function(){return B(_1x2(_1uF,_1ux,_1uu,_1wK,_1wE,function(_1yj){return new F(function(){return _1dj(_4l,_1xI,new T2(0,_1wE,_1yj));});}));}),_1yk=new T(function(){return B(_1x2(_1uF,_1ux,_1uu,_1wK,_1wF,function(_1yl){return new F(function(){return _1dj(_4l,_1xI,new T2(0,_1wF,_1yl));});}));}),_1ym=function(_1yn){return new F(function(){return A2(_1yk,E(_1yn).b,_1xE);});};return B(A(_1x2,[_1uF,_1ux,_1uu,_1wK,_1wD,function(_1yo){return new F(function(){return _1dj(_4l,_1xI,new T2(0,_1wD,_1yo));});},_1xB,function(_1yp){return new F(function(){return A2(_1yi,E(_1yp).b,_1ym);});}]));});return new T1(1,new T2(1,_1yh,new T2(1,_1xJ,_6)));};return new T1(1,new T2(1,new T1(0,_1xG),new T2(1,new T(function(){return new T1(0,B(_1vO(_1xB)));}),_6)));};},_1yq=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1yr=function(_1ys,_1yt){var _1yu=function(_){var _1yv=__app1(E(_1yq),E(_1yt)),_1yw=__eq(_1yv,E(_4r));return (E(_1yw)==0)?new T1(1,_1yv):_2o;};return new F(function(){return A2(_pC,_1ys,_1yu);});},_1yx=new T(function(){return B(unCStr("Canvas not found!"));}),_1yy=new T(function(){return B(err(_1yx));}),_1yz="canvas",_1yA=new T(function(){return eval("(Util.onload)");}),_1yB=function(_){var _1yC=__app1(E(_1yA),E(_4r)),_1yD=B(A3(_1yr,_2G,_1yz,_)),_1yE=E(_1yD);if(!_1yE._){return E(_1yy);}else{var _1yF=E(_1yE.a),_1yG=__app1(E(_1),_1yF);if(!_1yG){return E(_1yy);}else{var _1yH=__app1(E(_0),_1yF),_1yI=_1yH,_1yJ=new T(function(){return new T1(0,B(_1xx(function(_1yK,_1yL){return new T1(0,B(_1sO(new T2(0,_1yI,_1yF),_1yK,_1yL)));},_p4)));});return new F(function(){return _e(_1yJ,_6,_);});}}},_1yM=function(_){return new F(function(){return _1yB(_);});};
var hasteMain = function() {B(A(_1yM, [0]));};window.onload = hasteMain;