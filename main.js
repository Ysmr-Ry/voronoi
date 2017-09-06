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

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4){var _5=E(_3);return (_5._==0)?E(_4):new T2(1,_5.a,new T(function(){return B(_2(_5.b,_4));}));},_6=__Z,_7=0,_8=function(_9,_){while(1){var _a=E(_9);if(!_a._){return _7;}else{var _b=_a.b,_c=E(_a.a);switch(_c._){case 0:var _d=B(A1(_c.a,_));_9=B(_2(_b,new T2(1,_d,_6)));continue;case 1:_9=B(_2(_b,_c.a));continue;default:_9=_b;continue;}}}},_e=function(_f,_g,_){var _h=E(_f);switch(_h._){case 0:var _i=B(A1(_h.a,_));return new F(function(){return _8(B(_2(_g,new T2(1,_i,_6))),_);});break;case 1:return new F(function(){return _8(B(_2(_g,_h.a)),_);});break;default:return new F(function(){return _8(_g,_);});}},_j=function(_k,_l,_){var _m=B(A1(_k,_)),_n=B(A1(_l,_));return _m;},_o=function(_p,_q,_){var _r=B(A1(_p,_)),_s=B(A1(_q,_));return new T(function(){return B(A1(_r,_s));});},_t=function(_u,_v,_){var _w=B(A1(_v,_));return _u;},_x=function(_y,_z,_){var _A=B(A1(_z,_));return new T(function(){return B(A1(_y,_A));});},_B=new T2(0,_x,_t),_C=function(_D,_){return _D;},_E=function(_F,_G,_){var _H=B(A1(_F,_));return new F(function(){return A1(_G,_);});},_I=new T5(0,_B,_C,_o,_E,_j),_J=new T(function(){return B(unCStr("base"));}),_K=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_L=new T(function(){return B(unCStr("IOException"));}),_M=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_J,_K,_L),_N=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_M,_6,_6),_O=function(_P){return E(_N);},_Q=function(_R){return E(E(_R).a);},_S=function(_T,_U,_V){var _W=B(A1(_T,_)),_X=B(A1(_U,_)),_Y=hs_eqWord64(_W.a,_X.a);if(!_Y){return __Z;}else{var _Z=hs_eqWord64(_W.b,_X.b);return (!_Z)?__Z:new T1(1,_V);}},_10=function(_11){var _12=E(_11);return new F(function(){return _S(B(_Q(_12.a)),_O,_12.b);});},_13=new T(function(){return B(unCStr(": "));}),_14=new T(function(){return B(unCStr(")"));}),_15=new T(function(){return B(unCStr(" ("));}),_16=new T(function(){return B(unCStr("interrupted"));}),_17=new T(function(){return B(unCStr("system error"));}),_18=new T(function(){return B(unCStr("unsatisified constraints"));}),_19=new T(function(){return B(unCStr("user error"));}),_1a=new T(function(){return B(unCStr("permission denied"));}),_1b=new T(function(){return B(unCStr("illegal operation"));}),_1c=new T(function(){return B(unCStr("end of file"));}),_1d=new T(function(){return B(unCStr("resource exhausted"));}),_1e=new T(function(){return B(unCStr("resource busy"));}),_1f=new T(function(){return B(unCStr("does not exist"));}),_1g=new T(function(){return B(unCStr("already exists"));}),_1h=new T(function(){return B(unCStr("resource vanished"));}),_1i=new T(function(){return B(unCStr("timeout"));}),_1j=new T(function(){return B(unCStr("unsupported operation"));}),_1k=new T(function(){return B(unCStr("hardware fault"));}),_1l=new T(function(){return B(unCStr("inappropriate type"));}),_1m=new T(function(){return B(unCStr("invalid argument"));}),_1n=new T(function(){return B(unCStr("failed"));}),_1o=new T(function(){return B(unCStr("protocol error"));}),_1p=function(_1q,_1r){switch(E(_1q)){case 0:return new F(function(){return _2(_1g,_1r);});break;case 1:return new F(function(){return _2(_1f,_1r);});break;case 2:return new F(function(){return _2(_1e,_1r);});break;case 3:return new F(function(){return _2(_1d,_1r);});break;case 4:return new F(function(){return _2(_1c,_1r);});break;case 5:return new F(function(){return _2(_1b,_1r);});break;case 6:return new F(function(){return _2(_1a,_1r);});break;case 7:return new F(function(){return _2(_19,_1r);});break;case 8:return new F(function(){return _2(_18,_1r);});break;case 9:return new F(function(){return _2(_17,_1r);});break;case 10:return new F(function(){return _2(_1o,_1r);});break;case 11:return new F(function(){return _2(_1n,_1r);});break;case 12:return new F(function(){return _2(_1m,_1r);});break;case 13:return new F(function(){return _2(_1l,_1r);});break;case 14:return new F(function(){return _2(_1k,_1r);});break;case 15:return new F(function(){return _2(_1j,_1r);});break;case 16:return new F(function(){return _2(_1i,_1r);});break;case 17:return new F(function(){return _2(_1h,_1r);});break;default:return new F(function(){return _2(_16,_1r);});}},_1s=new T(function(){return B(unCStr("}"));}),_1t=new T(function(){return B(unCStr("{handle: "));}),_1u=function(_1v,_1w,_1x,_1y,_1z,_1A){var _1B=new T(function(){var _1C=new T(function(){var _1D=new T(function(){var _1E=E(_1y);if(!_1E._){return E(_1A);}else{var _1F=new T(function(){return B(_2(_1E,new T(function(){return B(_2(_14,_1A));},1)));},1);return B(_2(_15,_1F));}},1);return B(_1p(_1w,_1D));}),_1G=E(_1x);if(!_1G._){return E(_1C);}else{return B(_2(_1G,new T(function(){return B(_2(_13,_1C));},1)));}}),_1H=E(_1z);if(!_1H._){var _1I=E(_1v);if(!_1I._){return E(_1B);}else{var _1J=E(_1I.a);if(!_1J._){var _1K=new T(function(){var _1L=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1L));},1);return new F(function(){return _2(_1t,_1K);});}else{var _1M=new T(function(){var _1N=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1N));},1);return new F(function(){return _2(_1t,_1M);});}}}else{return new F(function(){return _2(_1H.a,new T(function(){return B(_2(_13,_1B));},1));});}},_1O=function(_1P){var _1Q=E(_1P);return new F(function(){return _1u(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_6);});},_1R=function(_1S){return new T2(0,_1T,_1S);},_1U=function(_1V,_1W,_1X){var _1Y=E(_1W);return new F(function(){return _1u(_1Y.a,_1Y.b,_1Y.c,_1Y.d,_1Y.f,_1X);});},_1Z=function(_20,_21){var _22=E(_20);return new F(function(){return _1u(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=44,_24=93,_25=91,_26=function(_27,_28,_29){var _2a=E(_28);if(!_2a._){return new F(function(){return unAppCStr("[]",_29);});}else{var _2b=new T(function(){var _2c=new T(function(){var _2d=function(_2e){var _2f=E(_2e);if(!_2f._){return E(new T2(1,_24,_29));}else{var _2g=new T(function(){return B(A2(_27,_2f.a,new T(function(){return B(_2d(_2f.b));})));});return new T2(1,_23,_2g);}};return B(_2d(_2a.b));});return B(A2(_27,_2a.a,_2c));});return new T2(1,_25,_2b);}},_2h=function(_2i,_2j){return new F(function(){return _26(_1Z,_2i,_2j);});},_2k=new T3(0,_1U,_1O,_2h),_1T=new T(function(){return new T5(0,_O,_2k,_1R,_10,_1O);}),_2l=new T(function(){return E(_1T);}),_2m=function(_2n){return E(E(_2n).c);},_2o=__Z,_2p=7,_2q=function(_2r){return new T6(0,_2o,_2p,_6,_2r,_2o,_2o);},_2s=function(_2t,_){var _2u=new T(function(){return B(A2(_2m,_2l,new T(function(){return B(A1(_2q,_2t));})));});return new F(function(){return die(_2u);});},_2v=function(_2w,_){return new F(function(){return _2s(_2w,_);});},_2x=function(_2y){return new F(function(){return A1(_2v,_2y);});},_2z=function(_2A,_2B,_){var _2C=B(A1(_2A,_));return new F(function(){return A2(_2B,_2C,_);});},_2D=new T5(0,_I,_2z,_E,_C,_2x),_2E=function(_2F){return E(_2F);},_2G=new T2(0,_2D,_2E),_2H=function(_2I){var _2J=E(_2I);return new T0(2);},_2K=function(_2L,_2M,_2N){return new T1(1,new T2(1,new T(function(){return B(A1(_2N,new T2(0,_7,_2M)));}),new T2(1,new T(function(){return B(A2(_2L,_2M,_2H));}),_6)));},_2O=function(_2P,_2Q,_2R){var _2S=new T(function(){return B(A1(_2P,_2R));}),_2T=function(_2U){var _2V=function(_2W){var _2X=E(_2W);return new F(function(){return A2(_2Q,_2X.b,function(_2Y){return new F(function(){return A1(_2U,new T2(0,_2X.a,E(_2Y).b));});});});};return new F(function(){return A1(_2S,_2V);});};return E(_2T);},_2Z=function(_30,_31,_32){var _33=new T(function(){return B(A1(_30,_32));}),_34=function(_35){var _36=function(_37){return new F(function(){return A1(_35,E(_37));});};return new F(function(){return A1(_33,function(_38){return new F(function(){return A2(_31,E(_38).b,_36);});});});};return E(_34);},_39=function(_3a,_3b,_3c){var _3d=new T(function(){return B(A1(_3a,_3c));}),_3e=function(_3f){var _3g=function(_3h){var _3i=E(_3h),_3j=function(_3k){var _3l=E(_3k);return new F(function(){return A1(_3f,new T2(0,new T(function(){return B(A1(_3i.a,_3l.a));}),_3l.b));});};return new F(function(){return A2(_3b,_3i.b,_3j);});};return new F(function(){return A1(_3d,_3g);});};return E(_3e);},_3m=function(_3n,_3o,_3p){return new F(function(){return _39(_3n,_3o,_3p);});},_3q=function(_3r,_3s,_3t){var _3u=new T(function(){return B(A1(_3s,_3t));}),_3v=function(_3w){var _3x=function(_3y){return new F(function(){return A1(_3w,new T(function(){return new T2(0,_3r,E(_3y).b);}));});};return new F(function(){return A1(_3u,_3x);});};return E(_3v);},_3z=function(_3A,_3B,_3C){var _3D=new T(function(){return B(A1(_3B,_3C));}),_3E=function(_3F){var _3G=function(_3H){var _3I=new T(function(){var _3J=E(_3H);return new T2(0,new T(function(){return B(A1(_3A,_3J.a));}),_3J.b);});return new F(function(){return A1(_3F,_3I);});};return new F(function(){return A1(_3D,_3G);});};return E(_3E);},_3K=function(_3n,_3o,_3p){return new F(function(){return _3z(_3n,_3o,_3p);});},_3L=new T2(0,_3K,_3q),_3M=function(_3N,_3O,_3P){return new F(function(){return A1(_3P,new T2(0,_3N,_3O));});},_3Q=function(_3n,_3o,_3p){return new F(function(){return _3M(_3n,_3o,_3p);});},_3R=new T5(0,_3L,_3Q,_3m,_2Z,_2O),_3S=function(_3T,_3U,_3V){var _3W=new T(function(){return B(A1(_3T,_3V));}),_3X=function(_3Y){return new F(function(){return A1(_3W,function(_3Z){return new F(function(){return A2(_3U,E(_3Z).b,_3Y);});});});};return E(_3X);},_40=function(_3n,_3o,_3p){return new F(function(){return _3S(_3n,_3o,_3p);});},_41=function(_42,_43,_44){var _45=new T(function(){return B(A1(_42,_44));}),_46=function(_47){return new F(function(){return A1(_45,function(_48){var _49=E(_48);return new F(function(){return A3(_43,_49.a,_49.b,_47);});});});};return E(_46);},_4a=function(_3n,_3o,_3p){return new F(function(){return _41(_3n,_3o,_3p);});},_4b=function(_4c,_4d){return new F(function(){return err(_4c);});},_4e=function(_3o,_3p){return new F(function(){return _4b(_3o,_3p);});},_4f=new T5(0,_3R,_4a,_40,_3Q,_4e),_4g=function(_4h,_4i,_4j){return new F(function(){return A1(_4h,function(_4k){return new F(function(){return A1(_4j,new T2(0,_4k,_4i));});});});},_4l=new T3(0,_4f,_4g,_2K),_4m=function(_){return new F(function(){return __jsNull();});},_4n=function(_4o){var _4p=B(A1(_4o,_));return E(_4p);},_4q=new T(function(){return B(_4n(_4m));}),_4r=new T(function(){return E(_4q);}),_4s=new T(function(){return eval("window.requestAnimationFrame");}),_4t=function(_4u,_4v,_4w,_4x){return function(_){var _4y=E(_4u),_4z=rMV(_4y),_4A=E(_4z);if(!_4A._){var _4B=B(A2(_4v,_4A.a,_)),_4C=function(_4D,_){var _4E=function(_){var _4F=rMV(_4y),_4G=function(_,_4H){var _4I=function(_){var _4J=__createJSFunc(2,function(_4K,_){var _4L=B(_4M(_,_));return _4r;}),_4N=__app1(E(_4s),_4J);return _7;},_4O=E(_4H);if(!_4O._){return new F(function(){return _4I(_);});}else{var _4P=B(A2(_4v,_4O.a,_));return new F(function(){return _4I(_);});}},_4Q=E(_4F);if(!_4Q._){return new F(function(){return _4G(_,new T1(1,_4Q.a));});}else{return new F(function(){return _4G(_,_2o);});}},_4M=function(_4R,_){return new F(function(){return _4E(_);});},_4S=B(_4M(_,_));return _4r;},_4T=__createJSFunc(2,E(_4C)),_4U=__app1(E(_4s),_4T);return new T(function(){return B(A1(_4x,new T2(0,_7,_4w)));});}else{var _4V=function(_4W,_){var _4X=function(_){var _4Y=rMV(_4y),_4Z=function(_,_50){var _51=function(_){var _52=__createJSFunc(2,function(_53,_){var _54=B(_55(_,_));return _4r;}),_56=__app1(E(_4s),_52);return _7;},_57=E(_50);if(!_57._){return new F(function(){return _51(_);});}else{var _58=B(A2(_4v,_57.a,_));return new F(function(){return _51(_);});}},_59=E(_4Y);if(!_59._){return new F(function(){return _4Z(_,new T1(1,_59.a));});}else{return new F(function(){return _4Z(_,_2o);});}},_55=function(_5a,_){return new F(function(){return _4X(_);});},_5b=B(_55(_,_));return _4r;},_5c=__createJSFunc(2,E(_4V)),_5d=__app1(E(_4s),_5c);return new T(function(){return B(A1(_4x,new T2(0,_7,_4w)));});}};},_5e=function(_){return _7;},_5f=function(_5g,_5h,_){return new F(function(){return _5e(_);});},_5i=false,_5j=function(_){return _5i;},_5k=function(_5l,_){return new F(function(){return _5j(_);});},_5m=new T1(0,1),_5n=function(_5o,_5p){var _5q=E(_5o);if(!_5q._){var _5r=_5q.a,_5s=E(_5p);if(!_5s._){var _5t=_5s.a;return (_5r!=_5t)?(_5r>_5t)?2:0:1;}else{var _5u=I_compareInt(_5s.a,_5r);return (_5u<=0)?(_5u>=0)?1:2:0;}}else{var _5v=_5q.a,_5w=E(_5p);if(!_5w._){var _5x=I_compareInt(_5v,_5w.a);return (_5x>=0)?(_5x<=0)?1:2:0;}else{var _5y=I_compare(_5v,_5w.a);return (_5y>=0)?(_5y<=0)?1:2:0;}}},_5z=new T(function(){return B(unCStr("base"));}),_5A=new T(function(){return B(unCStr("GHC.Exception"));}),_5B=new T(function(){return B(unCStr("ArithException"));}),_5C=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_5z,_5A,_5B),_5D=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_5C,_6,_6),_5E=function(_5F){return E(_5D);},_5G=function(_5H){var _5I=E(_5H);return new F(function(){return _S(B(_Q(_5I.a)),_5E,_5I.b);});},_5J=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_5K=new T(function(){return B(unCStr("denormal"));}),_5L=new T(function(){return B(unCStr("divide by zero"));}),_5M=new T(function(){return B(unCStr("loss of precision"));}),_5N=new T(function(){return B(unCStr("arithmetic underflow"));}),_5O=new T(function(){return B(unCStr("arithmetic overflow"));}),_5P=function(_5Q,_5R){switch(E(_5Q)){case 0:return new F(function(){return _2(_5O,_5R);});break;case 1:return new F(function(){return _2(_5N,_5R);});break;case 2:return new F(function(){return _2(_5M,_5R);});break;case 3:return new F(function(){return _2(_5L,_5R);});break;case 4:return new F(function(){return _2(_5K,_5R);});break;default:return new F(function(){return _2(_5J,_5R);});}},_5S=function(_5T){return new F(function(){return _5P(_5T,_6);});},_5U=function(_5V,_5W,_5X){return new F(function(){return _5P(_5W,_5X);});},_5Y=function(_5Z,_60){return new F(function(){return _26(_5P,_5Z,_60);});},_61=new T3(0,_5U,_5S,_5Y),_62=new T(function(){return new T5(0,_5E,_61,_63,_5G,_5S);}),_63=function(_64){return new T2(0,_62,_64);},_65=3,_66=new T(function(){return B(_63(_65));}),_67=new T(function(){return die(_66);}),_68=function(_69,_6a){var _6b=E(_69);return (_6b._==0)?_6b.a*Math.pow(2,_6a):I_toNumber(_6b.a)*Math.pow(2,_6a);},_6c=function(_6d,_6e){var _6f=E(_6d);if(!_6f._){var _6g=_6f.a,_6h=E(_6e);return (_6h._==0)?_6g==_6h.a:(I_compareInt(_6h.a,_6g)==0)?true:false;}else{var _6i=_6f.a,_6j=E(_6e);return (_6j._==0)?(I_compareInt(_6i,_6j.a)==0)?true:false:(I_compare(_6i,_6j.a)==0)?true:false;}},_6k=function(_6l){var _6m=E(_6l);if(!_6m._){return E(_6m.a);}else{return new F(function(){return I_toInt(_6m.a);});}},_6n=function(_6o,_6p){while(1){var _6q=E(_6o);if(!_6q._){var _6r=_6q.a,_6s=E(_6p);if(!_6s._){var _6t=_6s.a,_6u=addC(_6r,_6t);if(!E(_6u.b)){return new T1(0,_6u.a);}else{_6o=new T1(1,I_fromInt(_6r));_6p=new T1(1,I_fromInt(_6t));continue;}}else{_6o=new T1(1,I_fromInt(_6r));_6p=_6s;continue;}}else{var _6v=E(_6p);if(!_6v._){_6o=_6q;_6p=new T1(1,I_fromInt(_6v.a));continue;}else{return new T1(1,I_add(_6q.a,_6v.a));}}}},_6w=function(_6x,_6y){while(1){var _6z=E(_6x);if(!_6z._){var _6A=E(_6z.a);if(_6A==(-2147483648)){_6x=new T1(1,I_fromInt(-2147483648));continue;}else{var _6B=E(_6y);if(!_6B._){var _6C=_6B.a;return new T2(0,new T1(0,quot(_6A,_6C)),new T1(0,_6A%_6C));}else{_6x=new T1(1,I_fromInt(_6A));_6y=_6B;continue;}}}else{var _6D=E(_6y);if(!_6D._){_6x=_6z;_6y=new T1(1,I_fromInt(_6D.a));continue;}else{var _6E=I_quotRem(_6z.a,_6D.a);return new T2(0,new T1(1,_6E.a),new T1(1,_6E.b));}}}},_6F=new T1(0,0),_6G=function(_6H,_6I){while(1){var _6J=E(_6H);if(!_6J._){_6H=new T1(1,I_fromInt(_6J.a));continue;}else{return new T1(1,I_shiftLeft(_6J.a,_6I));}}},_6K=function(_6L,_6M,_6N){if(!B(_6c(_6N,_6F))){var _6O=B(_6w(_6M,_6N)),_6P=_6O.a;switch(B(_5n(B(_6G(_6O.b,1)),_6N))){case 0:return new F(function(){return _68(_6P,_6L);});break;case 1:if(!(B(_6k(_6P))&1)){return new F(function(){return _68(_6P,_6L);});}else{return new F(function(){return _68(B(_6n(_6P,_5m)),_6L);});}break;default:return new F(function(){return _68(B(_6n(_6P,_5m)),_6L);});}}else{return E(_67);}},_6Q=function(_6R,_6S){var _6T=E(_6R);if(!_6T._){var _6U=_6T.a,_6V=E(_6S);return (_6V._==0)?_6U>_6V.a:I_compareInt(_6V.a,_6U)<0;}else{var _6W=_6T.a,_6X=E(_6S);return (_6X._==0)?I_compareInt(_6W,_6X.a)>0:I_compare(_6W,_6X.a)>0;}},_6Y=new T1(0,1),_6Z=function(_70,_71){var _72=E(_70);if(!_72._){var _73=_72.a,_74=E(_71);return (_74._==0)?_73<_74.a:I_compareInt(_74.a,_73)>0;}else{var _75=_72.a,_76=E(_71);return (_76._==0)?I_compareInt(_75,_76.a)<0:I_compare(_75,_76.a)<0;}},_77=new T(function(){return B(unCStr("base"));}),_78=new T(function(){return B(unCStr("Control.Exception.Base"));}),_79=new T(function(){return B(unCStr("PatternMatchFail"));}),_7a=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_77,_78,_79),_7b=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7a,_6,_6),_7c=function(_7d){return E(_7b);},_7e=function(_7f){var _7g=E(_7f);return new F(function(){return _S(B(_Q(_7g.a)),_7c,_7g.b);});},_7h=function(_7i){return E(E(_7i).a);},_7j=function(_7k){return new T2(0,_7l,_7k);},_7m=function(_7n,_7o){return new F(function(){return _2(E(_7n).a,_7o);});},_7p=function(_7q,_7r){return new F(function(){return _26(_7m,_7q,_7r);});},_7s=function(_7t,_7u,_7v){return new F(function(){return _2(E(_7u).a,_7v);});},_7w=new T3(0,_7s,_7h,_7p),_7l=new T(function(){return new T5(0,_7c,_7w,_7j,_7e,_7h);}),_7x=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_7y=function(_7z,_7A){return new F(function(){return die(new T(function(){return B(A2(_2m,_7A,_7z));}));});},_7B=function(_7C,_64){return new F(function(){return _7y(_7C,_64);});},_7D=function(_7E,_7F){var _7G=E(_7F);if(!_7G._){return new T2(0,_6,_6);}else{var _7H=_7G.a;if(!B(A1(_7E,_7H))){return new T2(0,_6,_7G);}else{var _7I=new T(function(){var _7J=B(_7D(_7E,_7G.b));return new T2(0,_7J.a,_7J.b);});return new T2(0,new T2(1,_7H,new T(function(){return E(E(_7I).a);})),new T(function(){return E(E(_7I).b);}));}}},_7K=32,_7L=new T(function(){return B(unCStr("\n"));}),_7M=function(_7N){return (E(_7N)==124)?false:true;},_7O=function(_7P,_7Q){var _7R=B(_7D(_7M,B(unCStr(_7P)))),_7S=_7R.a,_7T=function(_7U,_7V){var _7W=new T(function(){var _7X=new T(function(){return B(_2(_7Q,new T(function(){return B(_2(_7V,_7L));},1)));});return B(unAppCStr(": ",_7X));},1);return new F(function(){return _2(_7U,_7W);});},_7Y=E(_7R.b);if(!_7Y._){return new F(function(){return _7T(_7S,_6);});}else{if(E(_7Y.a)==124){return new F(function(){return _7T(_7S,new T2(1,_7K,_7Y.b));});}else{return new F(function(){return _7T(_7S,_6);});}}},_7Z=function(_80){return new F(function(){return _7B(new T1(0,new T(function(){return B(_7O(_80,_7x));})),_7l);});},_81=function(_82){var _83=function(_84,_85){while(1){if(!B(_6Z(_84,_82))){if(!B(_6Q(_84,_82))){if(!B(_6c(_84,_82))){return new F(function(){return _7Z("GHC/Integer/Type.lhs:(555,5)-(557,32)|function l2");});}else{return E(_85);}}else{return _85-1|0;}}else{var _86=B(_6G(_84,1)),_87=_85+1|0;_84=_86;_85=_87;continue;}}};return new F(function(){return _83(_6Y,0);});},_88=function(_89){var _8a=E(_89);if(!_8a._){var _8b=_8a.a>>>0;if(!_8b){return -1;}else{var _8c=function(_8d,_8e){while(1){if(_8d>=_8b){if(_8d<=_8b){if(_8d!=_8b){return new F(function(){return _7Z("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_8e);}}else{return _8e-1|0;}}else{var _8f=imul(_8d,2)>>>0,_8g=_8e+1|0;_8d=_8f;_8e=_8g;continue;}}};return new F(function(){return _8c(1,0);});}}else{return new F(function(){return _81(_8a);});}},_8h=function(_8i){var _8j=E(_8i);if(!_8j._){var _8k=_8j.a>>>0;if(!_8k){return new T2(0,-1,0);}else{var _8l=function(_8m,_8n){while(1){if(_8m>=_8k){if(_8m<=_8k){if(_8m!=_8k){return new F(function(){return _7Z("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_8n);}}else{return _8n-1|0;}}else{var _8o=imul(_8m,2)>>>0,_8p=_8n+1|0;_8m=_8o;_8n=_8p;continue;}}};return new T2(0,B(_8l(1,0)),(_8k&_8k-1>>>0)>>>0&4294967295);}}else{var _8q=_8j.a;return new T2(0,B(_88(_8j)),I_compareInt(I_and(_8q,I_sub(_8q,I_fromInt(1))),0));}},_8r=function(_8s,_8t){var _8u=E(_8s);if(!_8u._){var _8v=_8u.a,_8w=E(_8t);return (_8w._==0)?_8v<=_8w.a:I_compareInt(_8w.a,_8v)>=0;}else{var _8x=_8u.a,_8y=E(_8t);return (_8y._==0)?I_compareInt(_8x,_8y.a)<=0:I_compare(_8x,_8y.a)<=0;}},_8z=function(_8A,_8B){while(1){var _8C=E(_8A);if(!_8C._){var _8D=_8C.a,_8E=E(_8B);if(!_8E._){return new T1(0,(_8D>>>0&_8E.a>>>0)>>>0&4294967295);}else{_8A=new T1(1,I_fromInt(_8D));_8B=_8E;continue;}}else{var _8F=E(_8B);if(!_8F._){_8A=_8C;_8B=new T1(1,I_fromInt(_8F.a));continue;}else{return new T1(1,I_and(_8C.a,_8F.a));}}}},_8G=function(_8H,_8I){while(1){var _8J=E(_8H);if(!_8J._){var _8K=_8J.a,_8L=E(_8I);if(!_8L._){var _8M=_8L.a,_8N=subC(_8K,_8M);if(!E(_8N.b)){return new T1(0,_8N.a);}else{_8H=new T1(1,I_fromInt(_8K));_8I=new T1(1,I_fromInt(_8M));continue;}}else{_8H=new T1(1,I_fromInt(_8K));_8I=_8L;continue;}}else{var _8O=E(_8I);if(!_8O._){_8H=_8J;_8I=new T1(1,I_fromInt(_8O.a));continue;}else{return new T1(1,I_sub(_8J.a,_8O.a));}}}},_8P=new T1(0,2),_8Q=function(_8R,_8S){var _8T=E(_8R);if(!_8T._){var _8U=(_8T.a>>>0&(2<<_8S>>>0)-1>>>0)>>>0,_8V=1<<_8S>>>0;return (_8V<=_8U)?(_8V>=_8U)?1:2:0;}else{var _8W=B(_8z(_8T,B(_8G(B(_6G(_8P,_8S)),_6Y)))),_8X=B(_6G(_6Y,_8S));return (!B(_6Q(_8X,_8W)))?(!B(_6Z(_8X,_8W)))?1:2:0;}},_8Y=function(_8Z,_90){while(1){var _91=E(_8Z);if(!_91._){_8Z=new T1(1,I_fromInt(_91.a));continue;}else{return new T1(1,I_shiftRight(_91.a,_90));}}},_92=function(_93,_94,_95,_96){var _97=B(_8h(_96)),_98=_97.a;if(!E(_97.b)){var _99=B(_88(_95));if(_99<((_98+_93|0)-1|0)){var _9a=_98+(_93-_94|0)|0;if(_9a>0){if(_9a>_99){if(_9a<=(_99+1|0)){if(!E(B(_8h(_95)).b)){return 0;}else{return new F(function(){return _68(_5m,_93-_94|0);});}}else{return 0;}}else{var _9b=B(_8Y(_95,_9a));switch(B(_8Q(_95,_9a-1|0))){case 0:return new F(function(){return _68(_9b,_93-_94|0);});break;case 1:if(!(B(_6k(_9b))&1)){return new F(function(){return _68(_9b,_93-_94|0);});}else{return new F(function(){return _68(B(_6n(_9b,_5m)),_93-_94|0);});}break;default:return new F(function(){return _68(B(_6n(_9b,_5m)),_93-_94|0);});}}}else{return new F(function(){return _68(_95,(_93-_94|0)-_9a|0);});}}else{if(_99>=_94){var _9c=B(_8Y(_95,(_99+1|0)-_94|0));switch(B(_8Q(_95,_99-_94|0))){case 0:return new F(function(){return _68(_9c,((_99-_98|0)+1|0)-_94|0);});break;case 2:return new F(function(){return _68(B(_6n(_9c,_5m)),((_99-_98|0)+1|0)-_94|0);});break;default:if(!(B(_6k(_9c))&1)){return new F(function(){return _68(_9c,((_99-_98|0)+1|0)-_94|0);});}else{return new F(function(){return _68(B(_6n(_9c,_5m)),((_99-_98|0)+1|0)-_94|0);});}}}else{return new F(function(){return _68(_95, -_98);});}}}else{var _9d=B(_88(_95))-_98|0,_9e=function(_9f){var _9g=function(_9h,_9i){if(!B(_8r(B(_6G(_9i,_94)),_9h))){return new F(function(){return _6K(_9f-_94|0,_9h,_9i);});}else{return new F(function(){return _6K((_9f-_94|0)+1|0,_9h,B(_6G(_9i,1)));});}};if(_9f>=_94){if(_9f!=_94){return new F(function(){return _9g(_95,new T(function(){return B(_6G(_96,_9f-_94|0));}));});}else{return new F(function(){return _9g(_95,_96);});}}else{return new F(function(){return _9g(new T(function(){return B(_6G(_95,_94-_9f|0));}),_96);});}};if(_93>_9d){return new F(function(){return _9e(_93);});}else{return new F(function(){return _9e(_9d);});}}},_9j=new T1(0,2147483647),_9k=new T(function(){return B(_6n(_9j,_6Y));}),_9l=function(_9m){var _9n=E(_9m);if(!_9n._){var _9o=E(_9n.a);return (_9o==(-2147483648))?E(_9k):new T1(0, -_9o);}else{return new T1(1,I_negate(_9n.a));}},_9p=new T(function(){return 0/0;}),_9q=new T(function(){return -1/0;}),_9r=new T(function(){return 1/0;}),_9s=0,_9t=function(_9u,_9v){if(!B(_6c(_9v,_6F))){if(!B(_6c(_9u,_6F))){if(!B(_6Z(_9u,_6F))){return new F(function(){return _92(-1021,53,_9u,_9v);});}else{return  -B(_92(-1021,53,B(_9l(_9u)),_9v));}}else{return E(_9s);}}else{return (!B(_6c(_9u,_6F)))?(!B(_6Z(_9u,_6F)))?E(_9r):E(_9q):E(_9p);}},_9w=function(_9x){var _9y=E(_9x);return new F(function(){return _9t(_9y.a,_9y.b);});},_9z=function(_9A){return 1/E(_9A);},_9B=function(_9C){var _9D=E(_9C);return (_9D!=0)?(_9D<=0)? -_9D:E(_9D):E(_9s);},_9E=function(_9F){var _9G=E(_9F);if(!_9G._){return _9G.a;}else{return new F(function(){return I_toNumber(_9G.a);});}},_9H=function(_9I){return new F(function(){return _9E(_9I);});},_9J=1,_9K=-1,_9L=function(_9M){var _9N=E(_9M);return (_9N<=0)?(_9N>=0)?E(_9N):E(_9K):E(_9J);},_9O=function(_9P,_9Q){return E(_9P)-E(_9Q);},_9R=function(_9S){return  -E(_9S);},_9T=function(_9U,_9V){return E(_9U)+E(_9V);},_9W=function(_9X,_9Y){return E(_9X)*E(_9Y);},_9Z={_:0,a:_9T,b:_9O,c:_9W,d:_9R,e:_9B,f:_9L,g:_9H},_a0=function(_a1,_a2){return E(_a1)/E(_a2);},_a3=new T4(0,_9Z,_a0,_9z,_9w),_a4=function(_a5,_a6){return new T2(1,_a5,new T1(0,_a6));},_a7=function(_a8,_a9,_aa){var _ab=E(_a9);if(!_ab._){return new F(function(){return A1(_aa,_ab.a);});}else{return new T2(1,_ab.a,new T(function(){return B(_a4(_ab.b,_aa));}));}},_ac=function(_ad){return new T1(0,_ad);},_ae=function(_af){return new F(function(){return err(_af);});},_ag=function(_ah){return new T5(0,_ah,function(_ai,_ad){return new F(function(){return _a7(_ah,_ai,_ad);});},function(_ai,_ad){return new F(function(){return _aj(_ah,_ai,_ad);});},_ac,_ae);},_ak=function(_al){return E(E(_al).b);},_aj=function(_am,_an,_ao){return new F(function(){return A3(_ak,B(_ag(_am)),_an,function(_ap){return E(_ao);});});},_aq=function(_ar){var _as=new T(function(){return B(_at(_ar));});return function(_au,_av){return new F(function(){return _aj(_as,_au,_av);});};},_aw=function(_ax,_ay){var _az=E(_ax);if(!_az._){var _aA=E(_ay);return (_aA._==0)?E(_az):new T2(1,_aA.a,new T2(1,_aA.b,new T1(0,function(_aB){return E(_az);})));}else{var _aC=function(_aD){var _aE=new T1(0,_aD),_aF=E(_ay);return (_aF._==0)?E(_aE):new T2(1,_aF.a,new T2(1,_aF.b,new T1(0,function(_aG){return E(_aE);})));};return new T2(1,_az.a,new T2(1,_az.b,new T1(0,_aC)));}},_aH=function(_aI,_aJ){var _aK=function(_aL){var _aM=E(_aJ);if(!_aM._){return new T1(0,new T(function(){return B(A1(_aL,_aM.a));}));}else{var _aN=function(_aO){return new T1(0,new T(function(){return B(A1(_aL,_aO));}));};return new T2(1,_aM.a,new T2(1,_aM.b,new T1(0,_aN)));}},_aP=E(_aI);if(!_aP._){return new F(function(){return _aK(_aP.a);});}else{return new T2(1,_aP.a,new T2(1,_aP.b,new T1(0,_aK)));}},_at=function(_aQ){return new T5(0,_aQ,_ac,_aH,new T(function(){return B(_aq(_aQ));}),_aw);},_aR=new T(function(){return new T2(0,_aS,_aT);}),_aU=new T(function(){return B(_at(_aR));}),_aV=new T(function(){return B(_ag(_aU));}),_aW=function(_aX){return E(E(_aX).d);},_aY=function(_aZ,_b0,_b1){var _b2=function(_b3){return new F(function(){return A2(_aW,_aZ,new T(function(){return B(A1(_b0,_b3));}));});};return new F(function(){return A3(_ak,_aZ,_b1,_b2);});},_aS=function(_ai,_ad){return new F(function(){return _aY(_aV,_ai,_ad);});},_aT=function(_b4,_b5){return new F(function(){return _aS(function(_b6){return E(_b4);},_b5);});},_b7=function(_b8,_b9,_ba){var _bb=E(_b8);return E(_b9)*(1-_bb)+E(_ba)*_bb;},_bc=function(_bd,_be){return (E(_bd)!=E(_be))?true:false;},_bf=function(_bg,_bh){return E(_bg)==E(_bh);},_bi=new T2(0,_bf,_bc),_bj=function(_bk,_bl){return E(_bk)<E(_bl);},_bm=function(_bn,_bo){return E(_bn)<=E(_bo);},_bp=function(_bq,_br){return E(_bq)>E(_br);},_bs=function(_bt,_bu){return E(_bt)>=E(_bu);},_bv=function(_bw,_bx){var _by=E(_bw),_bz=E(_bx);return (_by>=_bz)?(_by!=_bz)?2:1:0;},_bA=function(_bB,_bC){var _bD=E(_bB),_bE=E(_bC);return (_bD>_bE)?E(_bD):E(_bE);},_bF=function(_bG,_bH){var _bI=E(_bG),_bJ=E(_bH);return (_bI>_bJ)?E(_bJ):E(_bI);},_bK={_:0,a:_bi,b:_bv,c:_bj,d:_bm,e:_bp,f:_bs,g:_bA,h:_bF},_bL=function(_bM){var _bN=hs_intToInt64(_bM);return E(_bN);},_bO=function(_bP){var _bQ=E(_bP);if(!_bQ._){return new F(function(){return _bL(_bQ.a);});}else{return new F(function(){return I_toInt64(_bQ.a);});}},_bR=function(_bS){return new F(function(){return _bO(_bS);});},_bT=function(_bU,_bV){return new F(function(){return hs_timesInt64(E(_bU),E(_bV));});},_bW=function(_bX,_bY){return new F(function(){return hs_plusInt64(E(_bX),E(_bY));});},_bZ=function(_c0,_c1){return new F(function(){return hs_minusInt64(E(_c0),E(_c1));});},_c2=function(_c3){var _c4=hs_geInt64(_c3,new Long(0,0));if(!_c4){var _c5=hs_negateInt64(_c3);return E(_c5);}else{return E(_c3);}},_c6=function(_c7){return new F(function(){return _c2(E(_c7));});},_c8=function(_c9){return new F(function(){return hs_negateInt64(E(_c9));});},_ca=function(_cb){var _cc=hs_gtInt64(_cb,new Long(0,0));if(!_cc){var _cd=hs_eqInt64(_cb,new Long(0,0));if(!_cd){return new F(function(){return new Long(4294967295,-1);});}else{return new F(function(){return new Long(0,0);});}}else{return new F(function(){return new Long(1,0);});}},_ce=function(_cf){return new F(function(){return _ca(E(_cf));});},_cg={_:0,a:_bW,b:_bZ,c:_bT,d:_c8,e:_c6,f:_ce,g:_bR},_ch=true,_ci=new T1(0,0),_cj=function(_ck,_cl){while(1){var _cm=E(_ck);if(!_cm._){var _cn=_cm.a,_co=E(_cl);if(!_co._){return new T1(0,(_cn>>>0|_co.a>>>0)>>>0&4294967295);}else{_ck=new T1(1,I_fromInt(_cn));_cl=_co;continue;}}else{var _cp=E(_cl);if(!_cp._){_ck=_cm;_cl=new T1(1,I_fromInt(_cp.a));continue;}else{return new T1(1,I_or(_cm.a,_cp.a));}}}},_cq=function(_cr){var _cs=E(_cr);if(!_cs._){return E(_ci);}else{return new F(function(){return _cj(new T1(0,E(_cs.a)),B(_6G(B(_cq(_cs.b)),31)));});}},_ct=function(_cu,_cv){if(!E(_cu)){return new F(function(){return _9l(B(_cq(_cv)));});}else{return new F(function(){return _cq(_cv);});}},_cw=2147483647,_cx=2147483647,_cy=1,_cz=new T2(1,_cy,_6),_cA=new T2(1,_cx,_cz),_cB=new T2(1,_cw,_cA),_cC=new T(function(){return B(_ct(_ch,_cB));}),_cD=0,_cE=0,_cF=2,_cG=new T2(1,_cF,_6),_cH=new T2(1,_cE,_cG),_cI=new T2(1,_cD,_cH),_cJ=new T(function(){return B(_ct(_5i,_cI));}),_cK=new Long(2,0),_cL=new T(function(){return B(unCStr("Negative exponent"));}),_cM=new T(function(){return B(err(_cL));}),_cN=new Long(1,0),_cO=new Long(4294967295,2147483647),_cP=new Long(0,-2147483648),_cQ=new T2(0,_cP,_cO),_cR=new T1(0,1),_cS=function(_cT){return E(E(_cT).a);},_cU=function(_cV){return E(E(_cV).a);},_cW=function(_cX){return E(E(_cX).g);},_cY=function(_cZ){return E(E(_cZ).b);},_d0=function(_d1){return E(E(_d1).i);},_d2=function(_d3,_d4,_d5){var _d6=new T(function(){return B(_cW(new T(function(){return B(_cU(new T(function(){return B(_cS(_d3));})));})));}),_d7=new T(function(){return B(_cY(_d4));}),_d8=function(_d9){return (!B(_6Q(_d9,B(A2(_d0,_d3,_d7)))))?new T2(1,new T(function(){return B(A1(_d6,_d9));}),new T(function(){return B(_d8(B(_6n(_d9,_cR))));})):__Z;};return new F(function(){return _d8(B(A2(_d0,_d3,_d5)));});},_da=function(_db){return new F(function(){return _d2(_dc,_cQ,_db);});},_dd=new T1(0,0),_de=function(_df,_dg){var _dh=E(_df);if(!_dh._){var _di=_dh.a,_dj=E(_dg);return (_dj._==0)?_di>=_dj.a:I_compareInt(_dj.a,_di)<=0;}else{var _dk=_dh.a,_dl=E(_dg);return (_dl._==0)?I_compareInt(_dk,_dl.a)>=0:I_compare(_dk,_dl.a)>=0;}},_dm=function(_dn,_do,_dp,_dq,_dr){var _ds=function(_dt){if(!B(_6Q(_dt,_dr))){return new F(function(){return A2(_dn,_dt,new T(function(){return B(_ds(B(_6n(_dt,_dq))));}));});}else{return E(_do);}};return new F(function(){return _ds(_dp);});},_du=function(_dv,_dw,_dx,_dy,_dz){if(!B(_de(_dy,_dd))){var _dA=function(_dB){if(!B(_6Z(_dB,_dz))){return new F(function(){return A2(_dv,_dB,new T(function(){return B(_dA(B(_6n(_dB,_dy))));}));});}else{return E(_dw);}};return new F(function(){return _dA(_dx);});}else{return new F(function(){return _dm(_dv,_dw,_dx,_dy,_dz);});}},_dC=function(_dD){return E(E(_dD).a);},_dE=function(_dF,_dG,_dH,_dI){var _dJ=B(A2(_d0,_dF,_dI)),_dK=B(A2(_d0,_dF,_dH));if(!B(_de(_dJ,_dK))){var _dL=new T(function(){return B(_cW(new T(function(){return B(_cU(new T(function(){return B(_cS(_dF));})));})));}),_dM=function(_dN,_dO){return new T2(1,new T(function(){return B(A1(_dL,_dN));}),_dO);};return new F(function(){return _du(_dM,_6,_dK,B(_8G(_dJ,_dK)),B(A2(_d0,_dF,new T(function(){return B(_dC(_dG));}))));});}else{var _dP=new T(function(){return B(_cW(new T(function(){return B(_cU(new T(function(){return B(_cS(_dF));})));})));}),_dQ=function(_dR,_dS){return new T2(1,new T(function(){return B(A1(_dP,_dR));}),_dS);};return new F(function(){return _du(_dQ,_6,_dK,B(_8G(_dJ,_dK)),B(A2(_d0,_dF,new T(function(){return B(_cY(_dG));}))));});}},_dT=function(_dU,_db){return new F(function(){return _dE(_dc,_cQ,_dU,_db);});},_dV=function(_dW,_dX,_dY,_dZ){var _e0=B(A2(_d0,_dW,_dX)),_e1=new T(function(){return B(_cW(new T(function(){return B(_cU(new T(function(){return B(_cS(_dW));})));})));}),_e2=function(_e3,_e4){return new T2(1,new T(function(){return B(A1(_e1,_e3));}),_e4);};return new F(function(){return _du(_e2,_6,_e0,B(_8G(B(A2(_d0,_dW,_dY)),_e0)),B(A2(_d0,_dW,_dZ)));});},_e5=function(_e6,_dU,_db){return new F(function(){return _dV(_dc,_e6,_dU,_db);});},_e7=function(_e8,_e9,_ea){var _eb=new T(function(){return B(_cW(new T(function(){return B(_cU(new T(function(){return B(_cS(_e8));})));})));}),_ec=function(_ed){return (!B(_6Q(_ed,B(A2(_d0,_e8,_ea)))))?new T2(1,new T(function(){return B(A1(_eb,_ed));}),new T(function(){return B(_ec(B(_6n(_ed,_cR))));})):__Z;};return new F(function(){return _ec(B(A2(_d0,_e8,_e9)));});},_ee=function(_dU,_db){return new F(function(){return _e7(_dc,_dU,_db);});},_ef=new T(function(){return hs_intToInt64(2147483647);}),_eg=function(_eh){return new T1(0,_eh);},_ei=function(_ej){var _ek=hs_intToInt64(2147483647),_el=hs_leInt64(_ej,_ek);if(!_el){return new T1(1,I_fromInt64(_ej));}else{var _em=hs_intToInt64(-2147483648),_en=hs_geInt64(_ej,_em);if(!_en){return new T1(1,I_fromInt64(_ej));}else{var _eo=hs_int64ToInt(_ej);return new F(function(){return _eg(_eo);});}}},_ep=function(_eq){return new F(function(){return _ei(E(_eq));});},_er=function(_es){while(1){var _et=E(_es);if(!_et._){_es=new T1(1,I_fromInt(_et.a));continue;}else{return new F(function(){return I_toString(_et.a);});}}},_eu=function(_ev,_ew){return new F(function(){return _2(fromJSStr(B(_er(_ev))),_ew);});},_ex=41,_ey=40,_ez=new T1(0,0),_eA=function(_eB,_eC,_eD){if(_eB<=6){return new F(function(){return _eu(_eC,_eD);});}else{if(!B(_6Z(_eC,_ez))){return new F(function(){return _eu(_eC,_eD);});}else{return new T2(1,_ey,new T(function(){return B(_2(fromJSStr(B(_er(_eC))),new T2(1,_ex,_eD)));}));}}},_eE=function(_eF){return new F(function(){return _eA(0,B(_ep(_eF)),_6);});},_eG=function(_eH,_eI){return new F(function(){return _eA(0,B(_ei(E(_eH))),_eI);});},_eJ=function(_eK,_eL){return new F(function(){return _26(_eG,_eK,_eL);});},_eM=function(_eN,_eO){var _eP=new T(function(){return B(_ei(E(_eO)));});return function(_eQ){return new F(function(){return _eA(E(_eN),_eP,_eQ);});};},_eR=new T3(0,_eM,_eE,_eJ),_eS=new T2(1,_ex,_6),_eT=function(_eU,_eV,_eW){return new F(function(){return A1(_eU,new T2(1,_23,new T(function(){return B(A1(_eV,_eW));})));});},_eX=new T(function(){return B(unCStr(": empty list"));}),_eY=new T(function(){return B(unCStr("Prelude."));}),_eZ=function(_f0){return new F(function(){return err(B(_2(_eY,new T(function(){return B(_2(_f0,_eX));},1))));});},_f1=new T(function(){return B(unCStr("foldr1"));}),_f2=new T(function(){return B(_eZ(_f1));}),_f3=function(_f4,_f5){var _f6=E(_f5);if(!_f6._){return E(_f2);}else{var _f7=_f6.a,_f8=E(_f6.b);if(!_f8._){return E(_f7);}else{return new F(function(){return A2(_f4,_f7,new T(function(){return B(_f3(_f4,_f8));}));});}}},_f9=function(_fa,_fb){var _fc=jsShowI(_fa);return new F(function(){return _2(fromJSStr(_fc),_fb);});},_fd=function(_fe,_ff,_fg){if(_ff>=0){return new F(function(){return _f9(_ff,_fg);});}else{if(_fe<=6){return new F(function(){return _f9(_ff,_fg);});}else{return new T2(1,_ey,new T(function(){var _fh=jsShowI(_ff);return B(_2(fromJSStr(_fh),new T2(1,_ex,_fg)));}));}}},_fi=function(_fj){return new F(function(){return _fd(0,-2147483648,_fj);});},_fk=function(_fl){return new F(function(){return _fd(0,2147483647,_fl);});},_fm=new T2(1,_fk,_6),_fn=new T2(1,_fi,_fm),_fo=new T(function(){return B(_f3(_eT,_fn));}),_fp=new T(function(){return B(A1(_fo,_eS));}),_fq=new T2(1,_ey,_fp),_fr=new T(function(){return B(unAppCStr(") is outside of Int\'s bounds ",_fq));}),_fs=function(_ft){return E(E(_ft).b);},_fu=function(_fv,_fw,_fx){var _fy=new T(function(){var _fz=new T(function(){return B(unAppCStr("}: value (",new T(function(){return B(_2(B(A2(_fs,_fx,_fw)),_fr));})));},1);return B(_2(_fv,_fz));});return new F(function(){return err(B(unAppCStr("Enum.fromEnum{",_fy)));});},_fA=function(_fB,_fC,_fD){return new F(function(){return _fu(_fC,_fD,_fB);});},_fE=new T(function(){return B(unCStr("Int64"));}),_fF=function(_fG){return new F(function(){return _fA(_eR,_fE,_fG);});},_fH=function(_fI){return new F(function(){return _fF(_fI);});},_fJ=new T(function(){return hs_intToInt64(-2147483648);}),_fK=function(_fL){var _fM=hs_geInt64(_fL,E(_fJ));if(!_fM){return new F(function(){return _fH(_fL);});}else{var _fN=hs_leInt64(_fL,E(_ef));if(!_fN){return new F(function(){return _fH(_fL);});}else{var _fO=hs_int64ToInt(_fL);return E(_fO);}}},_fP=function(_fQ){return new F(function(){return _fK(E(_fQ));});},_fR=new T(function(){return B(unCStr("}: tried to take `pred\' of minBound"));}),_fS=function(_fT){return new F(function(){return err(B(unAppCStr("Enum.pred{",new T(function(){return B(_2(_fT,_fR));}))));});},_fU=function(_fV){return new F(function(){return _fS(_fV);});},_fW=new T(function(){return B(_fU(_fE));}),_fX=function(_fY){var _fZ=hs_neInt64(_fY,new Long(0,-2147483648));if(!_fZ){return E(_fW);}else{var _g0=hs_minusInt64(_fY,new Long(1,0));return E(_g0);}},_g1=function(_g2){return new F(function(){return _fX(E(_g2));});},_g3=new T(function(){return B(unCStr("}: tried to take `succ\' of maxBound"));}),_g4=function(_g5){return new F(function(){return err(B(unAppCStr("Enum.succ{",new T(function(){return B(_2(_g5,_g3));}))));});},_g6=function(_fV){return new F(function(){return _g4(_fV);});},_g7=new T(function(){return B(_g6(_fE));}),_g8=function(_g9){var _ga=hs_neInt64(_g9,new Long(4294967295,2147483647));if(!_ga){return E(_g7);}else{var _gb=hs_plusInt64(_g9,new Long(1,0));return E(_gb);}},_gc=function(_gd){return new F(function(){return _g8(E(_gd));});},_ge=function(_gf){return new F(function(){return hs_intToInt64(E(_gf));});},_gg=new T(function(){return {_:0,a:_gc,b:_g1,c:_ge,d:_fP,e:_da,f:_dT,g:_ee,h:_e5};}),_gh=function(_gi,_gj){var _gk=hs_minusInt64(_gi,_gj);return E(_gk);},_gl=function(_gm,_gn){var _go=hs_quotInt64(_gm,_gn);return E(_go);},_gp=function(_gq,_gr){var _gs=hs_intToInt64(1),_gt=_gs,_gu=hs_intToInt64(0),_gv=_gu,_gw=hs_gtInt64(_gq,_gv),_gx=function(_gy){var _gz=hs_ltInt64(_gq,_gv);if(!_gz){return new F(function(){return _gl(_gq,_gr);});}else{var _gA=hs_gtInt64(_gr,_gv);if(!_gA){return new F(function(){return _gl(_gq,_gr);});}else{var _gB=hs_plusInt64(_gq,_gt),_gC=hs_quotInt64(_gB,_gr);return new F(function(){return _gh(_gC,_gt);});}}};if(!_gw){return new F(function(){return _gx(_);});}else{var _gD=hs_ltInt64(_gr,_gv);if(!_gD){return new F(function(){return _gx(_);});}else{var _gE=hs_minusInt64(_gq,_gt),_gF=hs_quotInt64(_gE,_gr);return new F(function(){return _gh(_gF,_gt);});}}},_gG=0,_gH=new T(function(){return B(_63(_gG));}),_gI=new T(function(){return die(_gH);}),_gJ=function(_gK,_gL){var _gM=hs_eqInt64(_gL,new Long(0,0));if(!_gM){var _gN=hs_eqInt64(_gL,new Long(4294967295,-1));if(!_gN){return new F(function(){return _gp(_gK,_gL);});}else{var _gO=hs_eqInt64(_gK,new Long(0,-2147483648));if(!_gO){return new F(function(){return _gp(_gK,_gL);});}else{return E(_gI);}}}else{return E(_67);}},_gP=function(_gQ,_gR){return new F(function(){return _gJ(E(_gQ),E(_gR));});},_gS=new Long(0,0),_gT=function(_gU,_gV){var _gW=hs_plusInt64(_gU,_gV);return E(_gW);},_gX=function(_gY,_gZ){var _h0=hs_remInt64(_gY,_gZ),_h1=_h0,_h2=hs_intToInt64(0),_h3=_h2,_h4=hs_gtInt64(_gY,_h3),_h5=function(_h6){var _h7=hs_neInt64(_h1,_h3);if(!_h7){return E(_h3);}else{return new F(function(){return _gT(_h1,_gZ);});}},_h8=function(_h9){var _ha=hs_ltInt64(_gY,_h3);if(!_ha){return E(_h1);}else{var _hb=hs_gtInt64(_gZ,_h3);if(!_hb){return E(_h1);}else{return new F(function(){return _h5(_);});}}};if(!_h4){return new F(function(){return _h8(_);});}else{var _hc=hs_ltInt64(_gZ,_h3);if(!_hc){return new F(function(){return _h8(_);});}else{return new F(function(){return _h5(_);});}}},_hd=function(_he,_hf){var _hg=hs_eqInt64(_hf,new Long(0,0));if(!_hg){var _hh=hs_eqInt64(_hf,new Long(4294967295,-1));if(!_hh){return new T2(0,new T(function(){return B(_gp(_he,_hf));}),new T(function(){return B(_gX(_he,_hf));}));}else{var _hi=hs_eqInt64(_he,new Long(0,-2147483648));return (!_hi)?new T2(0,new T(function(){return B(_gp(_he,_hf));}),new T(function(){return B(_gX(_he,_hf));})):new T2(0,_gI,_gS);}}else{return E(_67);}},_hj=function(_hk,_hl){var _hm=B(_hd(E(_hk),E(_hl)));return new T2(0,_hm.a,_hm.b);},_hn=function(_ho,_hp){var _hq=hs_eqInt64(_hp,new Long(0,0));if(!_hq){var _hr=hs_eqInt64(_hp,new Long(4294967295,-1));if(!_hr){return new F(function(){return _gX(_ho,_hp);});}else{return new F(function(){return new Long(0,0);});}}else{return E(_67);}},_hs=function(_ht,_hu){return new F(function(){return _hn(E(_ht),E(_hu));});},_hv=function(_hw,_hx){var _hy=hs_eqInt64(_hx,new Long(0,0));if(!_hy){var _hz=hs_eqInt64(_hx,new Long(4294967295,-1));if(!_hz){var _hA=hs_quotInt64(_hw,_hx);return E(_hA);}else{var _hB=hs_eqInt64(_hw,new Long(0,-2147483648));if(!_hB){var _hC=hs_quotInt64(_hw,_hx);return E(_hC);}else{return E(_gI);}}}else{return E(_67);}},_hD=function(_hE,_hF){return new F(function(){return _hv(E(_hE),E(_hF));});},_hG=function(_hH,_hI){var _hJ=hs_eqInt64(_hI,new Long(0,0));if(!_hJ){var _hK=hs_eqInt64(_hI,new Long(4294967295,-1));if(!_hK){return new T2(0,new T(function(){return hs_quotInt64(_hH,_hI);}),new T(function(){return hs_remInt64(_hH,_hI);}));}else{var _hL=hs_eqInt64(_hH,new Long(0,-2147483648));return (!_hL)?new T2(0,new T(function(){return hs_quotInt64(_hH,_hI);}),new T(function(){return hs_remInt64(_hH,_hI);})):new T2(0,_gI,_gS);}}else{return E(_67);}},_hM=function(_hN,_hO){var _hP=B(_hG(E(_hN),E(_hO)));return new T2(0,_hP.a,_hP.b);},_hQ=function(_hR,_hS){var _hT=hs_eqInt64(_hS,new Long(0,0));if(!_hT){var _hU=hs_eqInt64(_hS,new Long(4294967295,-1));if(!_hU){var _hV=hs_remInt64(_hR,_hS);return E(_hV);}else{return new F(function(){return new Long(0,0);});}}else{return E(_67);}},_hW=function(_hX,_hY){return new F(function(){return _hQ(E(_hX),E(_hY));});},_hZ=function(_i0,_i1){return new F(function(){return hs_neInt64(E(_i0),E(_i1));});},_i2=function(_i3,_i4){return new F(function(){return hs_eqInt64(E(_i3),E(_i4));});},_i5=new T2(0,_i2,_hZ),_i6=function(_i7,_i8){return new F(function(){return hs_ltInt64(E(_i7),E(_i8));});},_i9=function(_ia,_ib){return new F(function(){return hs_leInt64(E(_ia),E(_ib));});},_ic=function(_id,_ie){return new F(function(){return hs_gtInt64(E(_id),E(_ie));});},_if=function(_ig,_ih){return new F(function(){return hs_geInt64(E(_ig),E(_ih));});},_ii=function(_ij,_ik){var _il=hs_eqInt64(_ij,_ik);if(!_il){var _im=hs_leInt64(_ij,_ik);return (!_im)?2:0;}else{return 1;}},_in=function(_io,_ip){return new F(function(){return _ii(E(_io),E(_ip));});},_iq=function(_ir,_is){var _it=E(_ir),_iu=E(_is),_iv=hs_leInt64(_it,_iu);return (!_iv)?E(_it):E(_iu);},_iw=function(_ix,_iy){var _iz=E(_ix),_iA=E(_iy),_iB=hs_leInt64(_iz,_iA);return (!_iB)?E(_iA):E(_iz);},_iC={_:0,a:_i5,b:_in,c:_i6,d:_i9,e:_ic,f:_if,g:_iq,h:_iw},_iD=new T1(0,1),_iE=new T1(0,0),_iF=function(_iG,_iH){while(1){var _iI=E(_iG);if(!_iI._){var _iJ=E(_iI.a);if(_iJ==(-2147483648)){_iG=new T1(1,I_fromInt(-2147483648));continue;}else{var _iK=E(_iH);if(!_iK._){return new T1(0,_iJ%_iK.a);}else{_iG=new T1(1,I_fromInt(_iJ));_iH=_iK;continue;}}}else{var _iL=_iI.a,_iM=E(_iH);return (_iM._==0)?new T1(1,I_rem(_iL,I_fromInt(_iM.a))):new T1(1,I_rem(_iL,_iM.a));}}},_iN=function(_iO,_iP){if(!B(_6c(_iP,_iE))){return new F(function(){return _iF(_iO,_iP);});}else{return E(_67);}},_iQ=function(_iR,_iS){while(1){if(!B(_6c(_iS,_iE))){var _iT=_iS,_iU=B(_iN(_iR,_iS));_iR=_iT;_iS=_iU;continue;}else{return E(_iR);}}},_iV=function(_iW){var _iX=E(_iW);if(!_iX._){var _iY=E(_iX.a);return (_iY==(-2147483648))?E(_9k):(_iY<0)?new T1(0, -_iY):E(_iX);}else{var _iZ=_iX.a;return (I_compareInt(_iZ,0)>=0)?E(_iX):new T1(1,I_negate(_iZ));}},_j0=function(_j1,_j2){while(1){var _j3=E(_j1);if(!_j3._){var _j4=E(_j3.a);if(_j4==(-2147483648)){_j1=new T1(1,I_fromInt(-2147483648));continue;}else{var _j5=E(_j2);if(!_j5._){return new T1(0,quot(_j4,_j5.a));}else{_j1=new T1(1,I_fromInt(_j4));_j2=_j5;continue;}}}else{var _j6=_j3.a,_j7=E(_j2);return (_j7._==0)?new T1(0,I_toInt(I_quot(_j6,I_fromInt(_j7.a)))):new T1(1,I_quot(_j6,_j7.a));}}},_j8=5,_j9=new T(function(){return B(_63(_j8));}),_ja=new T(function(){return die(_j9);}),_jb=function(_jc,_jd){if(!B(_6c(_jd,_iE))){var _je=B(_iQ(B(_iV(_jc)),B(_iV(_jd))));return (!B(_6c(_je,_iE)))?new T2(0,B(_j0(_jc,_je)),B(_j0(_jd,_je))):E(_67);}else{return E(_ja);}},_jf=function(_jg,_jh){while(1){var _ji=E(_jg);if(!_ji._){var _jj=_ji.a,_jk=E(_jh);if(!_jk._){var _jl=_jk.a;if(!(imul(_jj,_jl)|0)){return new T1(0,imul(_jj,_jl)|0);}else{_jg=new T1(1,I_fromInt(_jj));_jh=new T1(1,I_fromInt(_jl));continue;}}else{_jg=new T1(1,I_fromInt(_jj));_jh=_jk;continue;}}else{var _jm=E(_jh);if(!_jm._){_jg=_ji;_jh=new T1(1,I_fromInt(_jm.a));continue;}else{return new T1(1,I_mul(_ji.a,_jm.a));}}}},_jn=function(_jo){var _jp=B(_jb(B(_jf(B(_ei(E(_jo))),_iD)),_iD));return new T2(0,E(_jp.a),E(_jp.b));},_jq=new T3(0,_cg,_iC,_jn),_dc=new T(function(){return {_:0,a:_jq,b:_gg,c:_hD,d:_hW,e:_gP,f:_hs,g:_hM,h:_hj,i:_ep};}),_jr=function(_js){return E(E(_js).a);},_jt=function(_ju){return E(E(_ju).b);},_jv=function(_jw){return E(E(_jw).a);},_jx=new T1(0,2),_jy=function(_jz){return E(E(_jz).d);},_jA=function(_jB,_jC){var _jD=B(_cS(_jB)),_jE=new T(function(){return B(_cU(_jD));}),_jF=new T(function(){return B(A3(_jy,_jB,_jC,new T(function(){return B(A2(_cW,_jE,_jx));})));});return new F(function(){return A3(_jv,B(_jr(B(_jt(_jD)))),_jF,new T(function(){return B(A2(_cW,_jE,_iE));}));});},_jG=function(_jH,_jI,_jJ){while(1){var _jK=B((function(_jL,_jM,_jN){if(!B(_jA(_dc,_jM))){var _jO=hs_eqInt64(_jM,new Long(1,0));if(!_jO){var _jP=hs_minusInt64(_jM,new Long(1,0));_jH=new T(function(){return B(_bT(_jL,_jL));});_jI=B(_hv(_jP,new Long(2,0)));_jJ=new T(function(){return B(_bT(_jL,_jN));},1);return __continue;}else{var _jQ=hs_timesInt64(E(_jL),E(_jN));return E(_jQ);}}else{var _jR=B(_hv(_jM,new Long(2,0))),_jS=_jN;_jH=new T(function(){return B(_bT(_jL,_jL));});_jI=_jR;_jJ=_jS;return __continue;}})(_jH,_jI,_jJ));if(_jK!=__continue){return _jK;}}},_jT=function(_jU,_jV){while(1){var _jW=B((function(_jX,_jY){if(!B(_jA(_dc,_jY))){var _jZ=hs_eqInt64(_jY,new Long(1,0));if(!_jZ){var _k0=hs_minusInt64(_jY,new Long(1,0));return new F(function(){return _jG(new T(function(){return B(_bT(_jX,_jX));}),B(_hv(_k0,new Long(2,0))),_jX);});}else{return E(_jX);}}else{var _k1=B(_hv(_jY,new Long(2,0)));_jU=new T(function(){return B(_bT(_jX,_jX));});_jV=_k1;return __continue;}})(_jU,_jV));if(_jW!=__continue){return _jW;}}},_k2=function(_k3,_k4){var _k5=hs_ltInt64(_k4,new Long(0,0));if(!_k5){var _k6=hs_eqInt64(_k4,new Long(0,0));if(!_k6){return new F(function(){return _jT(_k3,_k4);});}else{return E(_cN);}}else{return E(_cM);}},_k7=new T(function(){return B(_k2(_cK,new Long(53,0)));}),_k8=new T(function(){return B(_9E(B(_ei(E(_k7)))));}),_k9=new T(function(){return hs_minusInt64(E(_k7),new Long(1,0));}),_ka=function(_kb,_kc){var _kd=hs_int64ToWord64(_kc),_ke=hs_int64ToWord64(_kb),_kf=hs_and64(_ke,_kd),_kg=hs_word64ToInt64(_kf);return E(_kg);},_kh=new T1(0,1),_ki=function(_kj,_kk){return new T2(0,E(_kj),E(_kk));},_kl=function(_km,_kn){var _ko=quot(_kn,52774),_kp=(imul(40692,_kn-(imul(_ko,52774)|0)|0)|0)-(imul(_ko,3791)|0)|0,_kq=new T(function(){if(_kp>=0){return _kp;}else{return _kp+2147483399|0;}}),_kr=quot(_km,53668),_ks=(imul(40014,_km-(imul(_kr,53668)|0)|0)|0)-(imul(_kr,12211)|0)|0,_kt=new T(function(){if(_ks>=0){return _ks;}else{return _ks+2147483563|0;}});return new T2(0,new T(function(){var _ku=E(_kt)-E(_kq)|0;if(_ku>=1){return _ku;}else{return _ku+2147483562|0;}}),new T(function(){return B(_ki(_kt,_kq));}));},_kv=new T1(0,2147483562),_kw=new T1(0,0),_kx=new T1(0,1000),_ky=function(_kz,_kA){var _kB=_kz%_kA;if(_kz<=0){if(_kz>=0){return E(_kB);}else{if(_kA<=0){return E(_kB);}else{var _kC=E(_kB);return (_kC==0)?0:_kC+_kA|0;}}}else{if(_kA>=0){if(_kz>=0){return E(_kB);}else{if(_kA<=0){return E(_kB);}else{var _kD=E(_kB);return (_kD==0)?0:_kD+_kA|0;}}}else{var _kE=E(_kB);return (_kE==0)?0:_kE+_kA|0;}}},_kF=function(_kG,_kH){while(1){var _kI=E(_kG);if(!_kI._){var _kJ=E(_kI.a);if(_kJ==(-2147483648)){_kG=new T1(1,I_fromInt(-2147483648));continue;}else{var _kK=E(_kH);if(!_kK._){return new T1(0,B(_ky(_kJ,_kK.a)));}else{_kG=new T1(1,I_fromInt(_kJ));_kH=_kK;continue;}}}else{var _kL=_kI.a,_kM=E(_kH);return (_kM._==0)?new T1(1,I_mod(_kL,I_fromInt(_kM.a))):new T1(1,I_mod(_kL,_kM.a));}}},_kN=function(_kO,_kP,_kQ,_kR){while(1){var _kS=B((function(_kT,_kU,_kV,_kW){if(!B(_6Q(_kU,_kV))){var _kX=B(_6n(B(_8G(_kV,_kU)),_kh)),_kY=function(_kZ,_l0,_l1){while(1){if(!B(_de(_kZ,B(_jf(_kX,_kx))))){var _l2=E(_l1),_l3=B(_kl(_l2.a,_l2.b)),_l4=B(_jf(_kZ,_kv)),_l5=B(_6n(B(_jf(_l0,_kv)),B(_8G(B(_eg(E(_l3.a))),_kh))));_kZ=_l4;_l0=_l5;_l1=_l3.b;continue;}else{return new T2(0,_l0,_l1);}}},_l6=B(_kY(_kh,_kw,_kW)),_l7=new T(function(){return B(A2(_cW,_kT,new T(function(){if(!B(_6c(_kX,_kw))){return B(_6n(_kU,B(_kF(_l6.a,_kX))));}else{return E(_67);}})));});return new T2(0,_l7,_l6.b);}else{var _l8=_kT,_l9=_kV,_la=_kU,_lb=_kW;_kO=_l8;_kP=_l9;_kQ=_la;_kR=_lb;return __continue;}})(_kO,_kP,_kQ,_kR));if(_kS!=__continue){return _kS;}}},_lc=function(_ld){var _le=B(_kN(_cg,_cJ,_cC,_ld));return new T2(0,new T(function(){return B(_9E(B(_ei(B(_ka(E(_k9),E(_le.a)))))))/E(_k8);}),_le.b);},_lf=function(_lg,_lh,_li){while(1){var _lj=B((function(_lk,_ll,_lm){if(_lk<=_ll){var _ln=new T(function(){var _lo=B(_lc(_lm));return new T2(0,_lo.a,_lo.b);});return new T2(0,new T(function(){var _lp=E(E(_ln).a);return 0.5*_lk+_lp*(0.5*_ll-0.5*_lk)+0.5*_lk+_lp*(0.5*_ll-0.5*_lk);}),new T(function(){return E(E(_ln).b);}));}else{var _lq=_ll,_lr=_lk,_ls=_lm;_lg=_lq;_lh=_lr;_li=_ls;return __continue;}})(_lg,_lh,_li));if(_lj!=__continue){return _lj;}}},_lt=1420103680,_lu=465,_lv=new T2(1,_lu,_6),_lw=new T2(1,_lt,_lv),_lx=new T(function(){return B(_ct(_ch,_lw));}),_ly=0,_lz=function(_lA,_lB){var _lC=E(_lB);if(!_lC){return E(_67);}else{var _lD=function(_lE){if(_lA<=0){if(_lA>=0){var _lF=quotRemI(_lA,_lC);return new T2(0,_lF.a,_lF.b);}else{if(_lC<=0){var _lG=quotRemI(_lA,_lC);return new T2(0,_lG.a,_lG.b);}else{var _lH=quotRemI(_lA+1|0,_lC);return new T2(0,_lH.a-1|0,(_lH.b+_lC|0)-1|0);}}}else{if(_lC>=0){if(_lA>=0){var _lI=quotRemI(_lA,_lC);return new T2(0,_lI.a,_lI.b);}else{if(_lC<=0){var _lJ=quotRemI(_lA,_lC);return new T2(0,_lJ.a,_lJ.b);}else{var _lK=quotRemI(_lA+1|0,_lC);return new T2(0,_lK.a-1|0,(_lK.b+_lC|0)-1|0);}}}else{var _lL=quotRemI(_lA-1|0,_lC);return new T2(0,_lL.a-1|0,(_lL.b+_lC|0)+1|0);}}};if(E(_lC)==(-1)){if(E(_lA)==(-2147483648)){return new T2(0,_gI,_ly);}else{return new F(function(){return _lD(_);});}}else{return new F(function(){return _lD(_);});}}},_lM=new T1(0,-1),_lN=function(_lO){var _lP=E(_lO);if(!_lP._){var _lQ=_lP.a;return (_lQ>=0)?(E(_lQ)==0)?E(_ci):E(_6Y):E(_lM);}else{var _lR=I_compareInt(_lP.a,0);return (_lR<=0)?(E(_lR)==0)?E(_ci):E(_lM):E(_6Y);}},_lS=function(_lT,_lU,_lV,_lW){var _lX=B(_jf(_lU,_lV));return new F(function(){return _jb(B(_jf(B(_jf(_lT,_lW)),B(_lN(_lX)))),B(_iV(_lX)));});},_lY=function(_lZ){return E(_lx);},_m0=new T1(0,1),_m1=function(_m2,_m3){var _m4=E(_m2);return new T2(0,_m4,new T(function(){var _m5=B(_m1(B(_6n(_m4,_m3)),_m3));return new T2(1,_m5.a,_m5.b);}));},_m6=function(_m7){var _m8=B(_m1(_m7,_m0));return new T2(1,_m8.a,_m8.b);},_m9=function(_ma,_mb){var _mc=B(_m1(_ma,new T(function(){return B(_8G(_mb,_ma));})));return new T2(1,_mc.a,_mc.b);},_md=function(_me,_mf,_mg){if(!B(_de(_mf,_dd))){var _mh=function(_mi){return (!B(_6Z(_mi,_mg)))?new T2(1,_mi,new T(function(){return B(_mh(B(_6n(_mi,_mf))));})):__Z;};return new F(function(){return _mh(_me);});}else{var _mj=function(_mk){return (!B(_6Q(_mk,_mg)))?new T2(1,_mk,new T(function(){return B(_mj(B(_6n(_mk,_mf))));})):__Z;};return new F(function(){return _mj(_me);});}},_ml=function(_mm,_mn,_mo){return new F(function(){return _md(_mm,B(_8G(_mn,_mm)),_mo);});},_mp=function(_mq,_mr){return new F(function(){return _md(_mq,_m0,_mr);});},_ms=function(_mt){return new F(function(){return _6k(_mt);});},_mu=function(_mv){return new F(function(){return _8G(_mv,_m0);});},_mw=function(_mx){return new F(function(){return _6n(_mx,_m0);});},_my=function(_mz){return new F(function(){return _eg(E(_mz));});},_mA={_:0,a:_mw,b:_mu,c:_my,d:_ms,e:_m6,f:_m9,g:_mp,h:_ml},_mB=function(_mC,_mD){if(_mC<=0){if(_mC>=0){return new F(function(){return quot(_mC,_mD);});}else{if(_mD<=0){return new F(function(){return quot(_mC,_mD);});}else{return quot(_mC+1|0,_mD)-1|0;}}}else{if(_mD>=0){if(_mC>=0){return new F(function(){return quot(_mC,_mD);});}else{if(_mD<=0){return new F(function(){return quot(_mC,_mD);});}else{return quot(_mC+1|0,_mD)-1|0;}}}else{return quot(_mC-1|0,_mD)-1|0;}}},_mE=function(_mF,_mG){while(1){var _mH=E(_mF);if(!_mH._){var _mI=E(_mH.a);if(_mI==(-2147483648)){_mF=new T1(1,I_fromInt(-2147483648));continue;}else{var _mJ=E(_mG);if(!_mJ._){return new T1(0,B(_mB(_mI,_mJ.a)));}else{_mF=new T1(1,I_fromInt(_mI));_mG=_mJ;continue;}}}else{var _mK=_mH.a,_mL=E(_mG);return (_mL._==0)?new T1(1,I_div(_mK,I_fromInt(_mL.a))):new T1(1,I_div(_mK,_mL.a));}}},_mM=function(_mN,_mO){if(!B(_6c(_mO,_iE))){return new F(function(){return _mE(_mN,_mO);});}else{return E(_67);}},_mP=function(_mQ,_mR){while(1){var _mS=E(_mQ);if(!_mS._){var _mT=E(_mS.a);if(_mT==(-2147483648)){_mQ=new T1(1,I_fromInt(-2147483648));continue;}else{var _mU=E(_mR);if(!_mU._){var _mV=_mU.a;return new T2(0,new T1(0,B(_mB(_mT,_mV))),new T1(0,B(_ky(_mT,_mV))));}else{_mQ=new T1(1,I_fromInt(_mT));_mR=_mU;continue;}}}else{var _mW=E(_mR);if(!_mW._){_mQ=_mS;_mR=new T1(1,I_fromInt(_mW.a));continue;}else{var _mX=I_divMod(_mS.a,_mW.a);return new T2(0,new T1(1,_mX.a),new T1(1,_mX.b));}}}},_mY=function(_mZ,_n0){if(!B(_6c(_n0,_iE))){var _n1=B(_mP(_mZ,_n0));return new T2(0,_n1.a,_n1.b);}else{return E(_67);}},_n2=function(_n3,_n4){if(!B(_6c(_n4,_iE))){return new F(function(){return _kF(_n3,_n4);});}else{return E(_67);}},_n5=function(_n6,_n7){if(!B(_6c(_n7,_iE))){return new F(function(){return _j0(_n6,_n7);});}else{return E(_67);}},_n8=function(_n9,_na){if(!B(_6c(_na,_iE))){var _nb=B(_6w(_n9,_na));return new T2(0,_nb.a,_nb.b);}else{return E(_67);}},_nc=function(_nd){return E(_nd);},_ne=function(_nf){return E(_nf);},_ng={_:0,a:_6n,b:_8G,c:_jf,d:_9l,e:_iV,f:_lN,g:_ne},_nh=function(_ni,_nj){var _nk=E(_ni);if(!_nk._){var _nl=_nk.a,_nm=E(_nj);return (_nm._==0)?_nl!=_nm.a:(I_compareInt(_nm.a,_nl)==0)?false:true;}else{var _nn=_nk.a,_no=E(_nj);return (_no._==0)?(I_compareInt(_nn,_no.a)==0)?false:true:(I_compare(_nn,_no.a)==0)?false:true;}},_np=new T2(0,_6c,_nh),_nq=function(_nr,_ns){return (!B(_8r(_nr,_ns)))?E(_nr):E(_ns);},_nt=function(_nu,_nv){return (!B(_8r(_nu,_nv)))?E(_nv):E(_nu);},_nw={_:0,a:_np,b:_5n,c:_6Z,d:_8r,e:_6Q,f:_de,g:_nq,h:_nt},_nx=function(_ny){return new T2(0,E(_ny),E(_cR));},_nz=new T3(0,_ng,_nw,_nx),_nA={_:0,a:_nz,b:_mA,c:_n5,d:_iN,e:_mM,f:_n2,g:_n8,h:_mY,i:_nc},_nB=new T1(0,0),_nC=function(_nD,_nE,_nF){var _nG=B(A1(_nD,_nE));if(!B(_6c(_nG,_nB))){return new F(function(){return _mE(B(_jf(_nE,_nF)),_nG);});}else{return E(_67);}},_nH=function(_nI,_nJ,_nK){var _nL=new T(function(){if(!B(_6c(_nK,_iE))){var _nM=B(_6w(_nJ,_nK));return new T2(0,_nM.a,_nM.b);}else{return E(_67);}}),_nN=new T(function(){return B(A2(_cW,B(_cU(B(_cS(_nI)))),new T(function(){return E(E(_nL).a);})));});return new T2(0,_nN,new T(function(){return new T2(0,E(E(_nL).b),E(_nK));}));},_nO=function(_nP){return E(E(_nP).b);},_nQ=function(_nR,_nS,_nT){var _nU=B(_nH(_nR,_nS,_nT)),_nV=_nU.a,_nW=E(_nU.b);if(!B(_6Z(B(_jf(_nW.a,_cR)),B(_jf(_iE,_nW.b))))){return E(_nV);}else{var _nX=B(_cU(B(_cS(_nR))));return new F(function(){return A3(_nO,_nX,_nV,new T(function(){return B(A2(_cW,_nX,_cR));}));});}},_nY=479723520,_nZ=40233135,_o0=new T2(1,_nZ,_6),_o1=new T2(1,_nY,_o0),_o2=new T(function(){return B(_ct(_ch,_o1));}),_o3=new T1(0,40587),_o4=function(_o5){var _o6=new T(function(){var _o7=B(_lS(_o5,_cR,_lx,_cR)),_o8=B(_lS(_o2,_cR,_lx,_cR)),_o9=B(_lS(_o7.a,_o7.b,_o8.a,_o8.b));return B(_nQ(_nA,_o9.a,_o9.b));});return new T2(0,new T(function(){return B(_6n(_o3,_o6));}),new T(function(){return B(_8G(_o5,B(_nC(_lY,B(_jf(_o6,_lx)),_o2))));}));},_oa=new T1(0,0),_ob=function(_oc,_){var _od=__get(_oc,0),_oe=__get(_oc,1),_of=Number(_od),_og=jsTrunc(_of),_oh=Number(_oe),_oi=jsTrunc(_oh);return new T2(0,_og,_oi);},_oj=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_ok=660865024,_ol=465661287,_om=new T2(1,_ol,_6),_on=new T2(1,_ok,_om),_oo=new T(function(){return B(_ct(_ch,_on));}),_op=function(_){var _oq=__app0(E(_oj)),_or=B(_ob(_oq,_));return new T(function(){var _os=E(_or);if(!B(_6c(_oo,_nB))){return B(_6n(B(_jf(B(_eg(E(_os.a))),_lx)),B(_mE(B(_jf(B(_jf(B(_eg(E(_os.b))),_lx)),_lx)),_oo))));}else{return E(_67);}});},_ot=new T1(0,12345),_ou=function(_){var _ov=B(_op(0)),_ow=B(_lS(B(_o4(_ov)).b,_cR,_lx,_cR)),_ox=_ow.b;if(!B(_6c(_ox,_kw))){var _oy=B(_6w(_ow.a,_ox));return new F(function(){return nMV(new T(function(){var _oz=B(_lz((B(_6k(B(_6n(B(_6n(B(_6n(B(_jf(_oy.a,_ot)),_oy.b)),_oa)),_kw))))>>>0&2147483647)>>>0&4294967295,2147483562));return new T2(0,E(_oz.b)+1|0,B(_ky(E(_oz.a),2147483398))+1|0);}));});}else{return E(_67);}},_oA=new T(function(){return B(_4n(_ou));}),_oB=function(_oC,_){var _oD=mMV(E(_oA),function(_oE){var _oF=E(_oC),_oG=B(_lf(E(_oF.a),E(_oF.b),_oE));return new T2(0,E(_oG.b),_oG.a);}),_oH=E(_oD);return _oD;},_oI=new T1(0,_7),_oJ=new T(function(){return B(unCStr("!!: negative index"));}),_oK=new T(function(){return B(_2(_eY,_oJ));}),_oL=new T(function(){return B(err(_oK));}),_oM=new T(function(){return B(unCStr("!!: index too large"));}),_oN=new T(function(){return B(_2(_eY,_oM));}),_oO=new T(function(){return B(err(_oN));}),_oP=function(_oQ,_oR){while(1){var _oS=E(_oQ);if(!_oS._){return E(_oO);}else{var _oT=E(_oR);if(!_oT){return E(_oS.a);}else{_oQ=_oS.b;_oR=_oT-1|0;continue;}}}},_oU=function(_oV,_oW){if(_oW>=0){return new F(function(){return _oP(_oV,_oW);});}else{return E(_oL);}},_oX=new T2(0,_2G,_C),_oY=new T0(2),_oZ=function(_p0){return new T0(2);},_p1=function(_p2,_p3,_p4){return function(_){var _p5=E(_p2),_p6=rMV(_p5),_p7=E(_p6);if(!_p7._){var _p8=new T(function(){var _p9=new T(function(){return B(A1(_p4,_7));});return B(_2(_p7.b,new T2(1,new T2(0,_p3,function(_pa){return E(_p9);}),_6)));}),_=wMV(_p5,new T2(0,_p7.a,_p8));return _oY;}else{var _pb=E(_p7.a);if(!_pb._){var _=wMV(_p5,new T2(0,_p3,_6));return new T(function(){return B(A1(_p4,_7));});}else{var _=wMV(_p5,new T1(1,_pb.b));return new T1(1,new T2(1,new T(function(){return B(A1(_p4,_7));}),new T2(1,new T(function(){return B(A2(_pb.a,_p3,_oZ));}),_6)));}}};},_pc=new T1(1,_6),_pd=function(_pe,_pf){return function(_){var _pg=E(_pe),_ph=rMV(_pg),_pi=E(_ph);if(!_pi._){var _pj=_pi.a,_pk=E(_pi.b);if(!_pk._){var _=wMV(_pg,_pc);return new T(function(){return B(A1(_pf,_pj));});}else{var _pl=E(_pk.a),_=wMV(_pg,new T2(0,_pl.a,_pk.b));return new T1(1,new T2(1,new T(function(){return B(A1(_pf,_pj));}),new T2(1,new T(function(){return B(A1(_pl.b,_oZ));}),_6)));}}else{var _pm=new T(function(){var _pn=function(_po){var _pp=new T(function(){return B(A1(_pf,_po));});return function(_pq){return E(_pp);};};return B(_2(_pi.a,new T2(1,_pn,_6)));}),_=wMV(_pg,new T1(1,_pm));return _oY;}};},_pr=function(_ps){return E(E(_ps).a);},_pt=function(_pu){return E(E(_pu).a);},_pv=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_pw=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_px=function(_py){return E(E(_py).b);},_pz=function(_pA){return E(E(_pA).b);},_pB=function(_pC,_pD,_pE){var _pF=B(_pr(_pC)),_pG=new T(function(){return B(_px(_pF));}),_pH=function(_pI){var _pJ=function(_){var _pK=E(_pD);if(!_pK._){var _pL=B(A1(_pI,_7)),_pM=__createJSFunc(0,function(_){var _pN=B(A1(_pL,_));return _4r;}),_pO=__app2(E(_pw),_pK.a,_pM);return new T(function(){var _pP=Number(_pO),_pQ=jsTrunc(_pP);return new T2(0,_pQ,E(_pK));});}else{var _pR=B(A1(_pI,_7)),_pS=__createJSFunc(0,function(_){var _pT=B(A1(_pR,_));return _4r;}),_pU=__app2(E(_pv),_pK.a,_pS);return new T(function(){var _pV=Number(_pU),_pW=jsTrunc(_pV);return new T2(0,_pW,E(_pK));});}};return new F(function(){return A1(_pG,_pJ);});},_pX=new T(function(){return B(A2(_pz,_pC,function(_pY){return E(_pE);}));});return new F(function(){return A3(_ak,B(_pt(_pF)),_pX,_pH);});},_pZ=new T1(1,_6),_q0=function(_q1,_q2){return function(_){var _q3=nMV(_pZ),_q4=_q3,_q5=function(_){var _q6=function(_){return new F(function(){return _e(new T(function(){return new T1(0,B(_p1(_q4,_7,_oZ)));}),_6,_);});},_q7=B(A(_pB,[_oX,new T(function(){return new T1(0,E(_q1));}),_q6,_]));return new T(function(){return new T1(0,B(_pd(_q4,_q2)));});};return new T1(0,_q5);};},_q8=0,_q9=new T1(1,_6),_qa=function(_qb,_qc,_qd){return function(_){var _qe=nMV(_q9),_qf=_qe;return new T(function(){var _qg=function(_qh){var _qi=new T(function(){return B(A1(_qd,new T2(0,_7,E(_qh).b)));}),_qj=function(_qk){return E(_qi);};return new T1(0,B(_pd(_qf,function(_ql){return new T1(0,B(_q0(_q8,_qj)));})));},_qm=function(_qn,_qo){return new T1(0,B(_p1(_qf,_7,function(_qp){return new F(function(){return A1(_qo,new T2(0,_qp,_qn));});})));};return B(A3(_qb,_qm,_qc,_qg));});};},_qq=function(_qr){return E(E(_qr).a);},_qs=function(_qt,_qu,_qv,_qw,_){var _qx=E(_qt);switch(_qx._){case 0:return new F(function(){return A(_qu,[_qx.a,_qv,_qw,_]);});break;case 1:var _qy=B(A1(_qx.a,_));return new F(function(){return A(_qu,[_qy,_qv,_qw,_]);});break;case 2:var _qz=rMV(E(E(_qx.a).c)),_qA=E(_qz);if(!_qA._){var _qB=new T(function(){return B(A1(_qx.b,new T(function(){return B(_qq(_qA.a));})));});return new F(function(){return A(_qu,[_qB,_qv,_qw,_]);});}else{return _7;}break;default:var _qC=rMV(E(E(_qx.a).c)),_qD=E(_qC);if(!_qD._){var _qE=B(A2(_qx.b,E(_qD.a).a,_));return new F(function(){return A(_qu,[_qE,_qv,_qw,_]);});}else{return _7;}}},_qF=function(_qG,_qH,_){var _qI=E(_qG);switch(_qI._){case 0:return new F(function(){return A2(_qH,_qI.a,_);});break;case 1:var _qJ=B(A1(_qI.a,_));return new F(function(){return A2(_qH,_qJ,_);});break;case 2:var _qK=rMV(E(E(_qI.a).c)),_qL=E(_qK);if(!_qL._){var _qM=new T(function(){return B(A1(_qI.b,new T(function(){return B(_qq(_qL.a));})));});return new F(function(){return A2(_qH,_qM,_);});}else{return _5i;}break;default:var _qN=rMV(E(E(_qI.a).c)),_qO=E(_qN);if(!_qO._){var _qP=B(A2(_qI.b,E(_qO.a).a,_));return new F(function(){return A2(_qH,_qP,_);});}else{return _5i;}}},_qQ=function(_){return _7;},_qR=new T(function(){return eval("(function(x1,y1,x2,y2,x,y,ctx,_){ctx.bezierCurveTo(x1,y1,x2,y2,x,y);})");}),_qS=new T(function(){return eval("(function(x,y,ctx,_){ctx.moveTo(x,y);})");}),_qT=new T(function(){return 4*(Math.sqrt(2)-1)/3;}),_qU=function(_qV,_qW,_qX){var _qY=function(_qZ,_r0,_r1,_){var _r2=function(_r3,_r4,_r5,_){return new F(function(){return _qs(_qX,function(_r6,_r7,_r8,_){var _r9=E(_qZ),_ra=E(_r3),_rb=E(_r6),_rc=E(_r7),_rd=_ra-_rb,_re=E(_r8),_rf=__app4(E(_qS),_r9,_rd,_rc,_re),_rg=E(_qT),_rh=E(_qR),_ri=__apply(_rh,new T2(1,_re,new T2(1,_rc,new T2(1,_ra,new T2(1,_r9+_rb,new T2(1,_ra-_rb*_rg,new T2(1,_r9+_rb,new T2(1,_rd,new T2(1,_r9+_rb*_rg,_6))))))))),_rj=__apply(_rh,new T2(1,_re,new T2(1,_rc,new T2(1,_ra+_rb,new T2(1,_r9,new T2(1,_ra+_rb,new T2(1,_r9+_rb*_rg,new T2(1,_ra+_rb*_rg,new T2(1,_r9+_rb,_6))))))))),_rk=__apply(_rh,new T2(1,_re,new T2(1,_rc,new T2(1,_ra,new T2(1,_r9-_rb,new T2(1,_ra+_rb*_rg,new T2(1,_r9-_rb,new T2(1,_ra+_rb,new T2(1,_r9-_rb*_rg,_6))))))))),_rl=__apply(_rh,new T2(1,_re,new T2(1,_rc,new T2(1,_rd,new T2(1,_r9,new T2(1,_rd,new T2(1,_r9-_rb*_rg,new T2(1,_ra-_rb*_rg,new T2(1,_r9-_rb,_6)))))))));return new F(function(){return _qQ(_);});},_r4,_r5,_);});};return new F(function(){return _qs(_qW,_r2,_r0,_r1,_);});},_rm=function(_rn,_){var _ro=E(_rn),_rp=function(_rq,_){var _rr=function(_rs,_){var _rt=function(_ru,_){return new T(function(){var _rv=E(_ru),_rw=E(_rs)-E(_ro.b),_rx=E(_rq)-E(_ro.a);return _rx*_rx+_rw*_rw<=_rv*_rv;});};return new F(function(){return _qF(_qX,_rt,_);});};return new F(function(){return _qF(_qW,_rr,_);});};return new F(function(){return _qF(_qV,_rp,_);});};return new T3(0,_rm,function(_ry,_rz,_){return new F(function(){return _qs(_qV,_qY,_ry,_rz,_);});},_7);},_rA=function(_rB){return E(E(_rB).a);},_rC=function(_rD){return E(E(_rD).c);},_rE=function(_rF){return E(E(_rF).b);},_rG=function(_rH,_rI,_rJ){return new T1(0,B(_p1(_rH,_rI,_rJ)));},_rK=function(_rL,_rM){return new T1(0,B(_pd(_rL,_rM)));},_rN=function(_rO,_rP,_rQ){var _rR=new T(function(){return B(_rE(_rO));}),_rS=B(_rA(_rO)),_rT=function(_rU,_rV){var _rW=new T(function(){return B(A1(_rR,function(_rX){return new F(function(){return _rG(_rP,_rV,_rX);});}));});return new F(function(){return A3(_rC,_rS,_rW,new T(function(){return B(A2(_aW,_rS,_rU));}));});},_rY=function(_rZ){var _s0=E(_rZ);return new F(function(){return _rT(_s0.a,_s0.b);});},_s1=function(_s2){return new F(function(){return A3(_ak,_rS,new T(function(){return B(A1(_rQ,_s2));}),_rY);});},_s3=new T(function(){return B(A2(_rE,_rO,function(_rX){return new F(function(){return _rK(_rP,_rX);});}));});return new F(function(){return A3(_ak,_rS,_s3,_s1);});},_s4=function(_s5,_s6,_s7){var _s8=new T(function(){return E(E(_s5).b);});return new F(function(){return A1(_s7,new T2(0,new T2(0,_7,new T2(0,new T(function(){return E(E(_s5).a);}),new T4(0,new T(function(){return E(E(_s8).a);}),new T(function(){return E(E(_s8).b);}),new T(function(){return E(E(_s8).c);}),_5i))),_s6));});},_s9=0,_sa=function(_sb,_sc,_sd,_se){var _sf=function(_sg,_sh,_si){return new F(function(){return A1(_si,new T2(0,new T2(0,_7,new T(function(){var _sj=E(_sg);return new T4(0,E(new T2(1,new T2(0,_sb,_sc),_sj.a)),_sj.b,E(_sj.c),E(_sj.d));})),_sh));});};return new F(function(){return A(_rN,[_4l,_sd,_sf,_sd,_se]);});},_sk=function(_sl,_sm,_sn,_so,_sp,_sq){var _sr=new T(function(){var _ss=new T(function(){return B(A1(_sn,_2E));}),_st=function(_su,_sv,_sw){var _sx=E(_su),_sy=E(_sx.b),_sz=new T(function(){var _sA=new T(function(){return B(A1(_ss,new T(function(){return B(_a0(_sy.c,_sm));})));});return B(A3(_sl,_sA,_sy.a,_sy.b));});return new F(function(){return A1(_sw,new T2(0,new T2(0,_7,new T2(0,_sx.a,new T4(0,_sz,_sp,_s9,_sy.d))),_sv));});};return B(_rN(_4l,_so,_st));}),_sB=new T(function(){return B(_rN(_4l,_so,_s4));}),_sC=new T(function(){var _sD=new T(function(){return B(A1(_sq,_5i));}),_sE=new T(function(){return B(A1(_sq,_ch));}),_sF=new T(function(){return B(A1(_sn,_2E));}),_sG=function(_sH,_sI,_sJ){var _sK=E(_sH),_sL=E(_sK.b),_sM=_sL.a,_sN=_sL.b;if(!E(_sL.d)){var _sO=E(_sm),_sP=E(_sL.c)+1,_sQ=function(_sR,_sS){var _sT=new T(function(){var _sU=new T(function(){return B(A1(_sF,new T(function(){return _sR/_sO;})));});return B(A3(_sl,_sU,_sM,_sN));}),_sV=new T4(0,_sM,_sN,_sS,_ch);if(_sR>=_sO){return new F(function(){return A2(_sE,_sI,function(_sW){return new F(function(){return A1(_sJ,new T2(0,new T2(0,_5i,new T2(0,_sT,_sV)),E(_sW).b));});});});}else{return new F(function(){return A1(_sJ,new T2(0,new T2(0,_ch,new T2(0,_sT,_sV)),_sI));});}};if(_sO>_sP){return new F(function(){return _sQ(_sP,_sP);});}else{return new F(function(){return _sQ(_sO,_sO);});}}else{return new F(function(){return A2(_sD,_sI,function(_sX){return new F(function(){return A1(_sJ,new T2(0,new T2(0,_5i,_sK),E(_sX).b));});});});}};return B(_rN(_4l,_so,_sG));}),_sY=function(_sZ,_t0){var _t1=new T(function(){return B(A2(_sr,_sZ,function(_t2){return new F(function(){return _sa(_sB,_sC,E(_t2).b,_t0);});}));}),_t3=function(_t4){var _t5=new T(function(){var _t6=E(_t4),_t7=E(_t6.a),_t8=E(_t6.b),_t9=E(_t8.a),_ta=E(_t8.b),_tb=E(_t8.c),_tc=E(_t8.d);return E(_t1);});return new T1(0,B(_p1(_so,_t4,function(_td){return E(_t5);})));};return new T1(0,B(_pd(_so,_t3)));};return E(_sY);},_te=1,_tf=function(_tg,_th){var _ti=new T(function(){var _tj=function(_tk,_tl,_tm){return new F(function(){return A1(_tm,new T2(0,new T2(0,_7,new T2(0,_th,new T4(0,_th,_th,_te,new T(function(){return E(E(E(_tk).b).d);})))),_tl));});};return B(_rN(_4l,_tg,_tj));}),_tn=function(_to,_tp){var _tq=new T(function(){return B(A2(_ti,_to,_tp));}),_tr=function(_ts){var _tt=new T(function(){var _tu=E(_ts),_tv=E(_tu.a),_tw=E(_tu.b),_tx=E(_tw.a),_ty=E(_tw.b),_tz=E(_tw.c),_tA=E(_tw.d);return E(_tq);});return new T1(0,B(_p1(_tg,_ts,function(_tB){return E(_tt);})));};return new T1(0,B(_pd(_tg,_tr)));};return E(_tn);},_tC=function(_tD,_tE){var _tF=E(_tD);if(!_tF._){return __Z;}else{var _tG=_tF.a,_tH=E(_tE);return (_tH==1)?new T2(1,new T(function(){var _tI=E(_tG),_tJ=E(_tI.b);return new T2(0,_tJ,_tI);}),_6):new T2(1,new T(function(){var _tK=E(_tG),_tL=E(_tK.b);return new T2(0,_tL,_tK);}),new T(function(){return B(_tC(_tF.b,_tH-1|0));}));}},_tM=function(_tN,_tO){while(1){var _tP=E(_tN);if(!_tP._){return E(_tO);}else{var _tQ=_tO+1|0;_tN=_tP.b;_tO=_tQ;continue;}}},_tR=function(_tS,_tT,_tU,_tV,_tW,_){var _tX=function(_,_tY){var _tZ=E(_tT);switch(_tZ._){case 0:return new F(function(){return A(_tU,[new T2(0,_tY,_tZ.a),_tV,_tW,_]);});break;case 1:var _u0=B(A1(_tZ.a,_));return new F(function(){return A(_tU,[new T2(0,_tY,_u0),_tV,_tW,_]);});break;case 2:var _u1=rMV(E(E(_tZ.a).c)),_u2=E(_u1);if(!_u2._){var _u3=new T(function(){return B(A1(_tZ.b,new T(function(){return B(_qq(_u2.a));})));});return new F(function(){return A(_tU,[new T2(0,_tY,_u3),_tV,_tW,_]);});}else{return _7;}break;default:var _u4=rMV(E(E(_tZ.a).c)),_u5=E(_u4);if(!_u5._){var _u6=B(A2(_tZ.b,E(_u5.a).a,_));return new F(function(){return A(_tU,[new T2(0,_tY,_u6),_tV,_tW,_]);});}else{return _7;}}},_u7=E(_tS);switch(_u7._){case 0:return new F(function(){return _tX(_,_u7.a);});break;case 1:var _u8=B(A1(_u7.a,_));return new F(function(){return _tX(_,_u8);});break;case 2:var _u9=rMV(E(E(_u7.a).c)),_ua=E(_u9);if(!_ua._){var _ub=new T(function(){return B(A1(_u7.b,new T(function(){return E(E(_ua.a).a);})));});return new F(function(){return _tX(_,_ub);});}else{return _7;}break;default:var _uc=rMV(E(E(_u7.a).c)),_ud=E(_uc);if(!_ud._){var _ue=B(A2(_u7.b,E(_ud.a).a,_));return new F(function(){return _tX(_,_ue);});}else{return _7;}}},_uf=new T(function(){return eval("(function(x,y,ctx,_){ctx.lineTo(x,y);})");}),_ug=function(_uh,_ui,_uj,_uk,_){var _ul=__app4(E(_uf),_uh,_ui,_uj,E(_uk));return new F(function(){return _qQ(_);});},_um=function(_un,_uo){var _up=function(_uq,_ur,_us,_){var _ut=E(_uo);return new F(function(){return _tR(_ut.a,_ut.b,function(_uu,_uv,_uw,_){var _ux=E(_uq),_uy=E(_uv),_uz=E(_uw),_uA=__app4(E(_qS),E(_ux.a),E(_ux.b),_uy,_uz),_uB=E(_uu);return new F(function(){return _ug(E(_uB.a),E(_uB.b),_uy,_uz,_);});},_ur,_us,_);});};return new T3(0,_5k,function(_uC,_uD,_){var _uE=E(_un);return new F(function(){return _tR(_uE.a,_uE.b,_up,_uC,_uD,_);});},_7);},_uF=function(_uG,_uH,_uI,_uJ,_uK){var _uL=E(_uK);if(!_uL._){return __Z;}else{var _uM=E(_uL.b),_uN=new T(function(){return B(_uF(new T(function(){return E(_uG)+E(_uJ);}),new T(function(){var _uO=E(_uH),_uP=E(_uJ);if(_uP>15){return _uO+1.5*_uP;}else{return _uO+22.5;}}),_ch,new T(function(){return E(_uJ)/2;}),_uL.c));});return new F(function(){return _2(B(_uF(new T(function(){return E(_uG)-E(_uJ);}),new T(function(){var _uQ=E(_uH),_uR=E(_uJ);if(_uR>15){return _uQ+1.5*_uR;}else{return _uQ+22.5;}}),_5i,new T(function(){return E(_uJ)/2;}),_uL.a)),new T2(1,new T5(0,new T2(0,_uG,_uH),new T2(0,E(_uM.a).a,E(_uM.b).a),_uL,_uJ,_uI),_uN));});}},_uS=function(_uT,_uU,_uV,_uW){while(1){var _uX=E(_uW);if(!_uX._){var _uY=E(_uX.b);if(_uT>_uY){_uU=_uY;_uV=_uX.c;_uW=_uX.e;continue;}else{_uW=_uX.d;continue;}}else{return new T2(0,_uU,_uV);}}},_uZ=function(_v0,_v1){while(1){var _v2=E(_v1);if(!_v2._){var _v3=E(_v2.b);if(_v0>_v3){return new T1(1,B(_uS(_v0,_v3,_v2.c,_v2.e)));}else{_v1=_v2.d;continue;}}else{return __Z;}}},_v4=new T(function(){return eval("(function(ctx,_){ctx.restore();})");}),_v5=new T(function(){return eval("(function(ctx,_){ctx.save();})");}),_v6=new T(function(){return eval("(function(x,y,ctx,_){ctx.scale(x,y);})");}),_v7=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");}),_v8=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");}),_v9=new T(function(){return eval("(function(x,y,ctx,_){ctx.translate(x,y);})");}),_va="alphabetic",_vb="middle",_vc="hanging",_vd="right",_ve="center",_vf="left",_vg="(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",_vh=function(_vi,_vj,_vk,_vl,_vm,_vn,_vo){var _vp=function(_vq,_vr,_vs,_){var _vt=function(_vu,_vv,_vw,_){var _vx=function(_vy,_vz,_vA,_){var _vB=function(_vC,_vD,_vE,_){var _vF=E(_vD),_vG=E(_vE),_vH=__app2(E(_v5),_vF,_vG),_vI=function(_vJ){var _vK=function(_vL){var _vM=eval(E(_vg)),_vN=__app4(E(_vM),E(_vi),_vJ,_vL,_vF),_vO=__app4(E(_v9),E(_vu),E(_vy),_vF,_vG),_vP=E(_vC)/10,_vQ=__app4(E(_v6),_vP,_vP,_vF,_vG);if(!_vG){var _vR=__app5(E(_v7),toJSStr(E(_vq)),0,0,_vF,false),_vS=__app2(E(_v4),_vF,false);return new F(function(){return _qQ(_);});}else{var _vT=__app5(E(_v8),toJSStr(E(_vq)),0,0,_vF,true),_vU=__app2(E(_v4),_vF,true);return new F(function(){return _qQ(_);});}};switch(E(_vl)){case 0:return new F(function(){return _vK(E(_vc));});break;case 1:return new F(function(){return _vK(E(_vb));});break;default:return new F(function(){return _vK(E(_va));});}};switch(E(_vk)){case 0:return new F(function(){return _vI(E(_vf));});break;case 1:return new F(function(){return _vI(E(_ve));});break;default:return new F(function(){return _vI(E(_vd));});}};return new F(function(){return _qs(_vo,_vB,_vz,_vA,_);});};return new F(function(){return _qs(_vn,_vx,_vv,_vw,_);});};return new F(function(){return _qs(_vm,_vt,_vr,_vs,_);});};return new T3(0,_5k,function(_ry,_rz,_){return new F(function(){return _qs(_vj,_vp,_ry,_rz,_);});},_7);},_vV=function(_vW,_vX,_vY,_vZ,_w0,_w1){return (_vW!=_vZ)?true:(E(_vX)!=E(_w0))?true:(E(_vY)!=E(_w1))?true:false;},_w2=function(_w3,_w4){var _w5=E(_w3),_w6=E(_w4);return new F(function(){return _vV(E(_w5.a),_w5.b,_w5.c,E(_w6.a),_w6.b,_w6.c);});},_w7=function(_w8,_w9){return E(_w8)==E(_w9);},_wa=function(_wb,_wc,_wd,_we,_wf,_wg){if(_wb!=_we){return false;}else{if(E(_wc)!=E(_wf)){return false;}else{return new F(function(){return _w7(_wd,_wg);});}}},_wh=function(_wi,_wj){var _wk=E(_wi),_wl=E(_wj);return new F(function(){return _wa(E(_wk.a),_wk.b,_wk.c,E(_wl.a),_wl.b,_wl.c);});},_wm=new T2(0,_wh,_w2),_wn=__Z,_wo=function(_wp){return E(E(_wp).b);},_wq=new T0(1),_wr=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_ws=function(_wt){return new F(function(){return err(_wr);});},_wu=new T(function(){return B(_ws(_));}),_wv=function(_ww,_wx,_wy,_wz){var _wA=E(_wz);if(!_wA._){var _wB=_wA.a,_wC=E(_wy);if(!_wC._){var _wD=_wC.a,_wE=_wC.b,_wF=_wC.c;if(_wD<=(imul(3,_wB)|0)){return new T5(0,(1+_wD|0)+_wB|0,E(_ww),_wx,E(_wC),E(_wA));}else{var _wG=E(_wC.d);if(!_wG._){var _wH=_wG.a,_wI=E(_wC.e);if(!_wI._){var _wJ=_wI.a,_wK=_wI.b,_wL=_wI.c,_wM=_wI.d;if(_wJ>=(imul(2,_wH)|0)){var _wN=function(_wO){var _wP=E(_wI.e);return (_wP._==0)?new T5(0,(1+_wD|0)+_wB|0,E(_wK),_wL,E(new T5(0,(1+_wH|0)+_wO|0,E(_wE),_wF,E(_wG),E(_wM))),E(new T5(0,(1+_wB|0)+_wP.a|0,E(_ww),_wx,E(_wP),E(_wA)))):new T5(0,(1+_wD|0)+_wB|0,E(_wK),_wL,E(new T5(0,(1+_wH|0)+_wO|0,E(_wE),_wF,E(_wG),E(_wM))),E(new T5(0,1+_wB|0,E(_ww),_wx,E(_wq),E(_wA))));},_wQ=E(_wM);if(!_wQ._){return new F(function(){return _wN(_wQ.a);});}else{return new F(function(){return _wN(0);});}}else{return new T5(0,(1+_wD|0)+_wB|0,E(_wE),_wF,E(_wG),E(new T5(0,(1+_wB|0)+_wJ|0,E(_ww),_wx,E(_wI),E(_wA))));}}else{return E(_wu);}}else{return E(_wu);}}}else{return new T5(0,1+_wB|0,E(_ww),_wx,E(_wq),E(_wA));}}else{var _wR=E(_wy);if(!_wR._){var _wS=_wR.a,_wT=_wR.b,_wU=_wR.c,_wV=_wR.e,_wW=E(_wR.d);if(!_wW._){var _wX=_wW.a,_wY=E(_wV);if(!_wY._){var _wZ=_wY.a,_x0=_wY.b,_x1=_wY.c,_x2=_wY.d;if(_wZ>=(imul(2,_wX)|0)){var _x3=function(_x4){var _x5=E(_wY.e);return (_x5._==0)?new T5(0,1+_wS|0,E(_x0),_x1,E(new T5(0,(1+_wX|0)+_x4|0,E(_wT),_wU,E(_wW),E(_x2))),E(new T5(0,1+_x5.a|0,E(_ww),_wx,E(_x5),E(_wq)))):new T5(0,1+_wS|0,E(_x0),_x1,E(new T5(0,(1+_wX|0)+_x4|0,E(_wT),_wU,E(_wW),E(_x2))),E(new T5(0,1,E(_ww),_wx,E(_wq),E(_wq))));},_x6=E(_x2);if(!_x6._){return new F(function(){return _x3(_x6.a);});}else{return new F(function(){return _x3(0);});}}else{return new T5(0,1+_wS|0,E(_wT),_wU,E(_wW),E(new T5(0,1+_wZ|0,E(_ww),_wx,E(_wY),E(_wq))));}}else{return new T5(0,3,E(_wT),_wU,E(_wW),E(new T5(0,1,E(_ww),_wx,E(_wq),E(_wq))));}}else{var _x7=E(_wV);return (_x7._==0)?new T5(0,3,E(_x7.b),_x7.c,E(new T5(0,1,E(_wT),_wU,E(_wq),E(_wq))),E(new T5(0,1,E(_ww),_wx,E(_wq),E(_wq)))):new T5(0,2,E(_ww),_wx,E(_wR),E(_wq));}}else{return new T5(0,1,E(_ww),_wx,E(_wq),E(_wq));}}},_x8=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_x9=function(_xa){return new F(function(){return err(_x8);});},_xb=new T(function(){return B(_x9(_));}),_xc=function(_xd,_xe,_xf,_xg){var _xh=E(_xf);if(!_xh._){var _xi=_xh.a,_xj=E(_xg);if(!_xj._){var _xk=_xj.a,_xl=_xj.b,_xm=_xj.c;if(_xk<=(imul(3,_xi)|0)){return new T5(0,(1+_xi|0)+_xk|0,E(_xd),_xe,E(_xh),E(_xj));}else{var _xn=E(_xj.d);if(!_xn._){var _xo=_xn.a,_xp=_xn.b,_xq=_xn.c,_xr=_xn.d,_xs=E(_xj.e);if(!_xs._){var _xt=_xs.a;if(_xo>=(imul(2,_xt)|0)){var _xu=function(_xv){var _xw=E(_xd),_xx=E(_xn.e);return (_xx._==0)?new T5(0,(1+_xi|0)+_xk|0,E(_xp),_xq,E(new T5(0,(1+_xi|0)+_xv|0,E(_xw),_xe,E(_xh),E(_xr))),E(new T5(0,(1+_xt|0)+_xx.a|0,E(_xl),_xm,E(_xx),E(_xs)))):new T5(0,(1+_xi|0)+_xk|0,E(_xp),_xq,E(new T5(0,(1+_xi|0)+_xv|0,E(_xw),_xe,E(_xh),E(_xr))),E(new T5(0,1+_xt|0,E(_xl),_xm,E(_wq),E(_xs))));},_xy=E(_xr);if(!_xy._){return new F(function(){return _xu(_xy.a);});}else{return new F(function(){return _xu(0);});}}else{return new T5(0,(1+_xi|0)+_xk|0,E(_xl),_xm,E(new T5(0,(1+_xi|0)+_xo|0,E(_xd),_xe,E(_xh),E(_xn))),E(_xs));}}else{return E(_xb);}}else{return E(_xb);}}}else{return new T5(0,1+_xi|0,E(_xd),_xe,E(_xh),E(_wq));}}else{var _xz=E(_xg);if(!_xz._){var _xA=_xz.a,_xB=_xz.b,_xC=_xz.c,_xD=_xz.e,_xE=E(_xz.d);if(!_xE._){var _xF=_xE.a,_xG=_xE.b,_xH=_xE.c,_xI=_xE.d,_xJ=E(_xD);if(!_xJ._){var _xK=_xJ.a;if(_xF>=(imul(2,_xK)|0)){var _xL=function(_xM){var _xN=E(_xd),_xO=E(_xE.e);return (_xO._==0)?new T5(0,1+_xA|0,E(_xG),_xH,E(new T5(0,1+_xM|0,E(_xN),_xe,E(_wq),E(_xI))),E(new T5(0,(1+_xK|0)+_xO.a|0,E(_xB),_xC,E(_xO),E(_xJ)))):new T5(0,1+_xA|0,E(_xG),_xH,E(new T5(0,1+_xM|0,E(_xN),_xe,E(_wq),E(_xI))),E(new T5(0,1+_xK|0,E(_xB),_xC,E(_wq),E(_xJ))));},_xP=E(_xI);if(!_xP._){return new F(function(){return _xL(_xP.a);});}else{return new F(function(){return _xL(0);});}}else{return new T5(0,1+_xA|0,E(_xB),_xC,E(new T5(0,1+_xF|0,E(_xd),_xe,E(_wq),E(_xE))),E(_xJ));}}else{return new T5(0,3,E(_xG),_xH,E(new T5(0,1,E(_xd),_xe,E(_wq),E(_wq))),E(new T5(0,1,E(_xB),_xC,E(_wq),E(_wq))));}}else{var _xQ=E(_xD);return (_xQ._==0)?new T5(0,3,E(_xB),_xC,E(new T5(0,1,E(_xd),_xe,E(_wq),E(_wq))),E(_xQ)):new T5(0,2,E(_xd),_xe,E(_wq),E(_xz));}}else{return new T5(0,1,E(_xd),_xe,E(_wq),E(_wq));}}},_xR=function(_xS,_xT){return new T5(0,1,E(_xS),_xT,E(_wq),E(_wq));},_xU=function(_xV,_xW,_xX){var _xY=E(_xX);if(!_xY._){return new F(function(){return _xc(_xY.b,_xY.c,_xY.d,B(_xU(_xV,_xW,_xY.e)));});}else{return new F(function(){return _xR(_xV,_xW);});}},_xZ=function(_y0,_y1,_y2){var _y3=E(_y2);if(!_y3._){return new F(function(){return _wv(_y3.b,_y3.c,B(_xZ(_y0,_y1,_y3.d)),_y3.e);});}else{return new F(function(){return _xR(_y0,_y1);});}},_y4=function(_y5,_y6,_y7,_y8,_y9,_ya,_yb){return new F(function(){return _wv(_y8,_y9,B(_xZ(_y5,_y6,_ya)),_yb);});},_yc=function(_yd,_ye,_yf,_yg,_yh,_yi,_yj,_yk){var _yl=E(_yf);if(!_yl._){var _ym=_yl.a,_yn=_yl.b,_yo=_yl.c,_yp=_yl.d,_yq=_yl.e;if((imul(3,_ym)|0)>=_yg){if((imul(3,_yg)|0)>=_ym){return new T5(0,(_ym+_yg|0)+1|0,E(_yd),_ye,E(_yl),E(new T5(0,_yg,E(_yh),_yi,E(_yj),E(_yk))));}else{return new F(function(){return _xc(_yn,_yo,_yp,B(_yc(_yd,_ye,_yq,_yg,_yh,_yi,_yj,_yk)));});}}else{return new F(function(){return _wv(_yh,_yi,B(_yr(_yd,_ye,_ym,_yn,_yo,_yp,_yq,_yj)),_yk);});}}else{return new F(function(){return _y4(_yd,_ye,_yg,_yh,_yi,_yj,_yk);});}},_yr=function(_ys,_yt,_yu,_yv,_yw,_yx,_yy,_yz){var _yA=E(_yz);if(!_yA._){var _yB=_yA.a,_yC=_yA.b,_yD=_yA.c,_yE=_yA.d,_yF=_yA.e;if((imul(3,_yu)|0)>=_yB){if((imul(3,_yB)|0)>=_yu){return new T5(0,(_yu+_yB|0)+1|0,E(_ys),_yt,E(new T5(0,_yu,E(_yv),_yw,E(_yx),E(_yy))),E(_yA));}else{return new F(function(){return _xc(_yv,_yw,_yx,B(_yc(_ys,_yt,_yy,_yB,_yC,_yD,_yE,_yF)));});}}else{return new F(function(){return _wv(_yC,_yD,B(_yr(_ys,_yt,_yu,_yv,_yw,_yx,_yy,_yE)),_yF);});}}else{return new F(function(){return _xU(_ys,_yt,new T5(0,_yu,E(_yv),_yw,E(_yx),E(_yy)));});}},_yG=function(_yH,_yI,_yJ,_yK){var _yL=E(_yJ);if(!_yL._){var _yM=_yL.a,_yN=_yL.b,_yO=_yL.c,_yP=_yL.d,_yQ=_yL.e,_yR=E(_yK);if(!_yR._){var _yS=_yR.a,_yT=_yR.b,_yU=_yR.c,_yV=_yR.d,_yW=_yR.e;if((imul(3,_yM)|0)>=_yS){if((imul(3,_yS)|0)>=_yM){return new T5(0,(_yM+_yS|0)+1|0,E(_yH),_yI,E(_yL),E(_yR));}else{return new F(function(){return _xc(_yN,_yO,_yP,B(_yc(_yH,_yI,_yQ,_yS,_yT,_yU,_yV,_yW)));});}}else{return new F(function(){return _wv(_yT,_yU,B(_yr(_yH,_yI,_yM,_yN,_yO,_yP,_yQ,_yV)),_yW);});}}else{return new F(function(){return _xU(_yH,_yI,_yL);});}}else{return new F(function(){return _xZ(_yH,_yI,_yK);});}},_yX=function(_yY,_yZ,_z0){var _z1=E(_yZ);if(!_z1._){return E(_z0);}else{var _z2=function(_z3,_z4){while(1){var _z5=E(_z4);if(!_z5._){var _z6=_z5.b,_z7=_z5.e;switch(B(A3(_wo,_yY,_z3,_z6))){case 0:return new F(function(){return _yG(_z6,_z5.c,B(_z2(_z3,_z5.d)),_z7);});break;case 1:return E(_z7);default:_z4=_z7;continue;}}else{return new T0(1);}}};return new F(function(){return _z2(_z1.a,_z0);});}},_z8=function(_z9,_za,_zb){var _zc=E(_za);if(!_zc._){return E(_zb);}else{var _zd=function(_ze,_zf){while(1){var _zg=E(_zf);if(!_zg._){var _zh=_zg.b,_zi=_zg.d;switch(B(A3(_wo,_z9,_zh,_ze))){case 0:return new F(function(){return _yG(_zh,_zg.c,_zi,B(_zd(_ze,_zg.e)));});break;case 1:return E(_zi);default:_zf=_zi;continue;}}else{return new T0(1);}}};return new F(function(){return _zd(_zc.a,_zb);});}},_zj=function(_zk,_zl,_zm,_zn){var _zo=E(_zl),_zp=E(_zn);if(!_zp._){var _zq=_zp.b,_zr=_zp.c,_zs=_zp.d,_zt=_zp.e;switch(B(A3(_wo,_zk,_zo,_zq))){case 0:return new F(function(){return _wv(_zq,_zr,B(_zj(_zk,_zo,_zm,_zs)),_zt);});break;case 1:return E(_zp);default:return new F(function(){return _xc(_zq,_zr,_zs,B(_zj(_zk,_zo,_zm,_zt)));});}}else{return new T5(0,1,E(_zo),_zm,E(_wq),E(_wq));}},_zu=function(_zv,_zw,_zx,_zy){return new F(function(){return _zj(_zv,_zw,_zx,_zy);});},_zz=function(_zA){return E(E(_zA).d);},_zB=function(_zC){return E(E(_zC).f);},_zD=function(_zE,_zF,_zG,_zH){var _zI=E(_zF);if(!_zI._){var _zJ=E(_zG);if(!_zJ._){return E(_zH);}else{var _zK=function(_zL,_zM){while(1){var _zN=E(_zM);if(!_zN._){if(!B(A3(_zB,_zE,_zN.b,_zL))){return E(_zN);}else{_zM=_zN.d;continue;}}else{return new T0(1);}}};return new F(function(){return _zK(_zJ.a,_zH);});}}else{var _zO=_zI.a,_zP=E(_zG);if(!_zP._){var _zQ=function(_zR,_zS){while(1){var _zT=E(_zS);if(!_zT._){if(!B(A3(_zz,_zE,_zT.b,_zR))){return E(_zT);}else{_zS=_zT.e;continue;}}else{return new T0(1);}}};return new F(function(){return _zQ(_zO,_zH);});}else{var _zU=function(_zV,_zW,_zX){while(1){var _zY=E(_zX);if(!_zY._){var _zZ=_zY.b;if(!B(A3(_zz,_zE,_zZ,_zV))){if(!B(A3(_zB,_zE,_zZ,_zW))){return E(_zY);}else{_zX=_zY.d;continue;}}else{_zX=_zY.e;continue;}}else{return new T0(1);}}};return new F(function(){return _zU(_zO,_zP.a,_zH);});}}},_A0=function(_A1,_A2,_A3,_A4,_A5){var _A6=E(_A5);if(!_A6._){var _A7=_A6.b,_A8=_A6.c,_A9=_A6.d,_Aa=_A6.e,_Ab=E(_A4);if(!_Ab._){var _Ac=_Ab.b,_Ad=function(_Ae){var _Af=new T1(1,E(_Ac));return new F(function(){return _yG(_Ac,_Ab.c,B(_A0(_A1,_A2,_Af,_Ab.d,B(_zD(_A1,_A2,_Af,_A6)))),B(_A0(_A1,_Af,_A3,_Ab.e,B(_zD(_A1,_Af,_A3,_A6)))));});};if(!E(_A9)._){return new F(function(){return _Ad(_);});}else{if(!E(_Aa)._){return new F(function(){return _Ad(_);});}else{return new F(function(){return _zu(_A1,_A7,_A8,_Ab);});}}}else{return new F(function(){return _yG(_A7,_A8,B(_yX(_A1,_A2,_A9)),B(_z8(_A1,_A3,_Aa)));});}}else{return E(_A4);}},_Ag=function(_Ah,_Ai,_Aj,_Ak,_Al,_Am,_An,_Ao,_Ap,_Aq,_Ar,_As,_At){var _Au=function(_Av){var _Aw=new T1(1,E(_Al));return new F(function(){return _yG(_Al,_Am,B(_A0(_Ah,_Ai,_Aw,_An,B(_zD(_Ah,_Ai,_Aw,new T5(0,_Ap,E(_Aq),_Ar,E(_As),E(_At)))))),B(_A0(_Ah,_Aw,_Aj,_Ao,B(_zD(_Ah,_Aw,_Aj,new T5(0,_Ap,E(_Aq),_Ar,E(_As),E(_At)))))));});};if(!E(_As)._){return new F(function(){return _Au(_);});}else{if(!E(_At)._){return new F(function(){return _Au(_);});}else{return new F(function(){return _zu(_Ah,_Aq,_Ar,new T5(0,_Ak,E(_Al),_Am,E(_An),E(_Ao)));});}}},_Ax=function(_Ay,_Az){var _AA=E(_Ay);if(!_AA._){var _AB=E(_Az);if(!_AB._){return new F(function(){return _Ag(_bK,_wn,_wn,_AA.a,_AA.b,_AA.c,_AA.d,_AA.e,_AB.a,_AB.b,_AB.c,_AB.d,_AB.e);});}else{return E(_AA);}}else{return E(_Az);}},_AC=function(_AD,_AE,_AF,_AG){return (_AD!=_AF)?true:(E(_AE)!=E(_AG))?true:false;},_AH=function(_AI,_AJ){var _AK=E(_AI),_AL=E(_AJ);return new F(function(){return _AC(E(_AK.a),_AK.b,E(_AL.a),_AL.b);});},_AM=function(_AN,_AO,_AP,_AQ){if(_AN!=_AP){return false;}else{return new F(function(){return _bf(_AO,_AQ);});}},_AR=function(_AS,_AT){var _AU=E(_AS),_AV=E(_AT);return new F(function(){return _AM(E(_AU.a),_AU.b,E(_AV.a),_AV.b);});},_AW=new T2(0,_AR,_AH),_AX=function(_AY,_AZ,_B0,_B1,_B2,_B3,_B4,_B5,_B6,_B7,_B8,_B9,_Ba,_Bb,_Bc,_Bd,_Be,_Bf,_Bg,_Bh,_Bi,_Bj,_Bk,_Bl){if(_AY!=_Ba){return false;}else{if(_AZ!=_Bb){return false;}else{if(_B0!=_Bc){return false;}else{if(_B1!=_Bd){return false;}else{if(_B2!=_Be){return false;}else{if(_B3!=_Bf){return false;}else{if(_B4!=_Bg){return false;}else{if(_B5!=_Bh){return false;}else{if(_B6!=_Bi){return false;}else{if(_B7!=_Bj){return false;}else{if(E(_B8)!=E(_Bk)){return false;}else{return new F(function(){return _bf(_B9,_Bl);});}}}}}}}}}}}},_Bm=function(_Bn,_Bo){var _Bp=E(_Bn),_Bq=E(_Bp.a),_Br=E(_Bp.b),_Bs=E(_Bp.c),_Bt=E(_Bp.e),_Bu=E(_Bo),_Bv=E(_Bu.a),_Bw=E(_Bu.b),_Bx=E(_Bu.c),_By=E(_Bu.e);return new F(function(){return _AX(_Bq.a,_Bq.b,_Bq.c,_Br.a,_Br.b,_Br.c,_Bs.a,_Bs.b,_Bs.c,_Bp.d,_Bt.a,_Bt.b,_Bv.a,_Bv.b,_Bv.c,_Bw.a,_Bw.b,_Bw.c,_Bx.a,_Bx.b,_Bx.c,_Bu.d,_By.a,_By.b);});},_Bz=function(_BA,_BB,_BC,_BD,_BE,_BF){if(_BA!=_BD){return false;}else{var _BG=E(_BB),_BH=E(_BE);if(E(_BG.a)!=E(_BH.a)){return false;}else{if(E(_BG.b)!=E(_BH.b)){return false;}else{if(E(_BG.c)!=E(_BH.c)){return false;}else{return new F(function(){return _Bm(_BC,_BF);});}}}}},_BI=function(_BJ,_BK){var _BL=E(_BJ),_BM=E(_BK);return new F(function(){return _Bz(E(_BL.a),_BL.b,_BL.c,E(_BM.a),_BM.b,_BM.c);});},_BN=function(_BO,_BP,_BQ,_BR,_BS,_BT){if(_BO!=_BR){return true;}else{var _BU=E(_BP),_BV=E(_BS);if(E(_BU.a)!=E(_BV.a)){return true;}else{if(E(_BU.b)!=E(_BV.b)){return true;}else{if(E(_BU.c)!=E(_BV.c)){return true;}else{var _BW=E(_BQ),_BX=E(_BW.a),_BY=E(_BW.b),_BZ=E(_BW.c),_C0=E(_BW.e),_C1=E(_BT),_C2=E(_C1.a),_C3=E(_C1.b),_C4=E(_C1.c),_C5=E(_C1.e);return (_BX.a!=_C2.a)?true:(_BX.b!=_C2.b)?true:(_BX.c!=_C2.c)?true:(_BY.a!=_C3.a)?true:(_BY.b!=_C3.b)?true:(_BY.c!=_C3.c)?true:(_BZ.a!=_C4.a)?true:(_BZ.b!=_C4.b)?true:(_BZ.c!=_C4.c)?true:(_BW.d!=_C1.d)?true:(E(_C0.a)!=E(_C5.a))?true:(E(_C0.b)!=E(_C5.b))?true:false;}}}}},_C6=function(_C7,_C8){var _C9=E(_C7),_Ca=E(_C8);return new F(function(){return _BN(E(_C9.a),_C9.b,_C9.c,E(_Ca.a),_Ca.b,_Ca.c);});},_Cb=new T2(0,_BI,_C6),_Cc=function(_Cd,_Ce,_Cf,_Cg,_Ch,_Ci,_Cj,_Ck,_Cl,_Cm,_Cn,_Co,_Cp,_Cq,_Cr,_Cs,_Ct,_Cu,_Cv,_Cw,_Cx,_Cy,_Cz,_CA){if(_Cd>=_Cp){if(_Cd!=_Cp){return 2;}else{if(_Ce>=_Cq){if(_Ce!=_Cq){return 2;}else{if(_Cf>=_Cr){if(_Cf!=_Cr){return 2;}else{if(_Cg>=_Cs){if(_Cg!=_Cs){return 2;}else{if(_Ch>=_Ct){if(_Ch!=_Ct){return 2;}else{if(_Ci>=_Cu){if(_Ci!=_Cu){return 2;}else{if(_Cj>=_Cv){if(_Cj!=_Cv){return 2;}else{if(_Ck>=_Cw){if(_Ck!=_Cw){return 2;}else{if(_Cl>=_Cx){if(_Cl!=_Cx){return 2;}else{if(_Cm>=_Cy){if(_Cm!=_Cy){return 2;}else{var _CB=E(_Cn),_CC=E(_Cz);if(_CB>=_CC){if(_CB!=_CC){return 2;}else{return new F(function(){return _bv(_Co,_CA);});}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}},_CD=function(_CE,_CF){var _CG=E(_CE),_CH=E(_CG.a),_CI=E(_CG.b),_CJ=E(_CG.c),_CK=E(_CG.e),_CL=E(_CF),_CM=E(_CL.a),_CN=E(_CL.b),_CO=E(_CL.c),_CP=E(_CL.e);return new F(function(){return _Cc(_CH.a,_CH.b,_CH.c,_CI.a,_CI.b,_CI.c,_CJ.a,_CJ.b,_CJ.c,_CG.d,_CK.a,_CK.b,_CM.a,_CM.b,_CM.c,_CN.a,_CN.b,_CN.c,_CO.a,_CO.b,_CO.c,_CL.d,_CP.a,_CP.b);});},_CQ=function(_CR,_CS,_CT,_CU,_CV,_CW){if(_CR>=_CU){if(_CR!=_CU){return 2;}else{var _CX=E(_CS),_CY=E(_CV),_CZ=E(_CX.a),_D0=E(_CY.a);if(_CZ>=_D0){if(_CZ!=_D0){return 2;}else{var _D1=E(_CX.b),_D2=E(_CY.b);if(_D1>=_D2){if(_D1!=_D2){return 2;}else{var _D3=E(_CX.c),_D4=E(_CY.c);if(_D3>=_D4){if(_D3!=_D4){return 2;}else{return new F(function(){return _CD(_CT,_CW);});}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}},_D5=function(_D6,_D7){var _D8=E(_D6),_D9=E(_D7);return new F(function(){return _CQ(E(_D8.a),_D8.b,_D8.c,E(_D9.a),_D9.b,_D9.c);});},_Da=function(_Db,_Dc,_Dd,_De,_Df,_Dg,_Dh,_Di,_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy){if(_Db>=_Dn){if(_Db!=_Dn){return false;}else{if(_Dc>=_Do){if(_Dc!=_Do){return false;}else{if(_Dd>=_Dp){if(_Dd!=_Dp){return false;}else{if(_De>=_Dq){if(_De!=_Dq){return false;}else{if(_Df>=_Dr){if(_Df!=_Dr){return false;}else{if(_Dg>=_Ds){if(_Dg!=_Ds){return false;}else{if(_Dh>=_Dt){if(_Dh!=_Dt){return false;}else{if(_Di>=_Du){if(_Di!=_Du){return false;}else{if(_Dj>=_Dv){if(_Dj!=_Dv){return false;}else{if(_Dk>=_Dw){if(_Dk!=_Dw){return false;}else{var _Dz=E(_Dl),_DA=E(_Dx);if(_Dz>=_DA){if(_Dz!=_DA){return false;}else{return new F(function(){return _bj(_Dm,_Dy);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_DB=function(_DC,_DD){var _DE=E(_DC),_DF=E(_DE.a),_DG=E(_DE.b),_DH=E(_DE.c),_DI=E(_DE.e),_DJ=E(_DD),_DK=E(_DJ.a),_DL=E(_DJ.b),_DM=E(_DJ.c),_DN=E(_DJ.e);return new F(function(){return _Da(_DF.a,_DF.b,_DF.c,_DG.a,_DG.b,_DG.c,_DH.a,_DH.b,_DH.c,_DE.d,_DI.a,_DI.b,_DK.a,_DK.b,_DK.c,_DL.a,_DL.b,_DL.c,_DM.a,_DM.b,_DM.c,_DJ.d,_DN.a,_DN.b);});},_DO=function(_DP,_DQ,_DR,_DS,_DT,_DU){if(_DP>=_DS){if(_DP!=_DS){return false;}else{var _DV=E(_DQ),_DW=E(_DT),_DX=E(_DV.a),_DY=E(_DW.a);if(_DX>=_DY){if(_DX!=_DY){return false;}else{var _DZ=E(_DV.b),_E0=E(_DW.b);if(_DZ>=_E0){if(_DZ!=_E0){return false;}else{var _E1=E(_DV.c),_E2=E(_DW.c);if(_E1>=_E2){if(_E1!=_E2){return false;}else{return new F(function(){return _DB(_DR,_DU);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_E3=function(_E4,_E5){var _E6=E(_E4),_E7=E(_E5);return new F(function(){return _DO(E(_E6.a),_E6.b,_E6.c,E(_E7.a),_E7.b,_E7.c);});},_E8=function(_E9,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh,_Ei,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew){if(_E9>=_El){if(_E9!=_El){return false;}else{if(_Ea>=_Em){if(_Ea!=_Em){return false;}else{if(_Eb>=_En){if(_Eb!=_En){return false;}else{if(_Ec>=_Eo){if(_Ec!=_Eo){return false;}else{if(_Ed>=_Ep){if(_Ed!=_Ep){return false;}else{if(_Ee>=_Eq){if(_Ee!=_Eq){return false;}else{if(_Ef>=_Er){if(_Ef!=_Er){return false;}else{if(_Eg>=_Es){if(_Eg!=_Es){return false;}else{if(_Eh>=_Et){if(_Eh!=_Et){return false;}else{if(_Ei>=_Eu){if(_Ei!=_Eu){return false;}else{var _Ex=E(_Ej),_Ey=E(_Ev);if(_Ex>=_Ey){if(_Ex!=_Ey){return false;}else{return new F(function(){return _bm(_Ek,_Ew);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_Ez=function(_EA,_EB){var _EC=E(_EA),_ED=E(_EC.a),_EE=E(_EC.b),_EF=E(_EC.c),_EG=E(_EC.e),_EH=E(_EB),_EI=E(_EH.a),_EJ=E(_EH.b),_EK=E(_EH.c),_EL=E(_EH.e);return new F(function(){return _E8(_ED.a,_ED.b,_ED.c,_EE.a,_EE.b,_EE.c,_EF.a,_EF.b,_EF.c,_EC.d,_EG.a,_EG.b,_EI.a,_EI.b,_EI.c,_EJ.a,_EJ.b,_EJ.c,_EK.a,_EK.b,_EK.c,_EH.d,_EL.a,_EL.b);});},_EM=function(_EN,_EO,_EP,_EQ,_ER,_ES){if(_EN>=_EQ){if(_EN!=_EQ){return false;}else{var _ET=E(_EO),_EU=E(_ER),_EV=E(_ET.a),_EW=E(_EU.a);if(_EV>=_EW){if(_EV!=_EW){return false;}else{var _EX=E(_ET.b),_EY=E(_EU.b);if(_EX>=_EY){if(_EX!=_EY){return false;}else{var _EZ=E(_ET.c),_F0=E(_EU.c);if(_EZ>=_F0){if(_EZ!=_F0){return false;}else{return new F(function(){return _Ez(_EP,_ES);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_F1=function(_F2,_F3){var _F4=E(_F2),_F5=E(_F3);return new F(function(){return _EM(E(_F4.a),_F4.b,_F4.c,E(_F5.a),_F5.b,_F5.c);});},_F6=function(_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo,_Fp,_Fq,_Fr,_Fs,_Ft,_Fu){if(_F7>=_Fj){if(_F7!=_Fj){return true;}else{if(_F8>=_Fk){if(_F8!=_Fk){return true;}else{if(_F9>=_Fl){if(_F9!=_Fl){return true;}else{if(_Fa>=_Fm){if(_Fa!=_Fm){return true;}else{if(_Fb>=_Fn){if(_Fb!=_Fn){return true;}else{if(_Fc>=_Fo){if(_Fc!=_Fo){return true;}else{if(_Fd>=_Fp){if(_Fd!=_Fp){return true;}else{if(_Fe>=_Fq){if(_Fe!=_Fq){return true;}else{if(_Ff>=_Fr){if(_Ff!=_Fr){return true;}else{if(_Fg>=_Fs){if(_Fg!=_Fs){return true;}else{var _Fv=E(_Fh),_Fw=E(_Ft);if(_Fv>=_Fw){if(_Fv!=_Fw){return true;}else{return new F(function(){return _bp(_Fi,_Fu);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_Fx=function(_Fy,_Fz){var _FA=E(_Fy),_FB=E(_FA.a),_FC=E(_FA.b),_FD=E(_FA.c),_FE=E(_FA.e),_FF=E(_Fz),_FG=E(_FF.a),_FH=E(_FF.b),_FI=E(_FF.c),_FJ=E(_FF.e);return new F(function(){return _F6(_FB.a,_FB.b,_FB.c,_FC.a,_FC.b,_FC.c,_FD.a,_FD.b,_FD.c,_FA.d,_FE.a,_FE.b,_FG.a,_FG.b,_FG.c,_FH.a,_FH.b,_FH.c,_FI.a,_FI.b,_FI.c,_FF.d,_FJ.a,_FJ.b);});},_FK=function(_FL,_FM,_FN,_FO,_FP,_FQ){if(_FL>=_FO){if(_FL!=_FO){return true;}else{var _FR=E(_FM),_FS=E(_FP),_FT=E(_FR.a),_FU=E(_FS.a);if(_FT>=_FU){if(_FT!=_FU){return true;}else{var _FV=E(_FR.b),_FW=E(_FS.b);if(_FV>=_FW){if(_FV!=_FW){return true;}else{var _FX=E(_FR.c),_FY=E(_FS.c);if(_FX>=_FY){if(_FX!=_FY){return true;}else{return new F(function(){return _Fx(_FN,_FQ);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_FZ=function(_G0,_G1){var _G2=E(_G0),_G3=E(_G1);return new F(function(){return _FK(E(_G2.a),_G2.b,_G2.c,E(_G3.a),_G3.b,_G3.c);});},_G4=function(_G5,_G6,_G7,_G8,_G9,_Ga,_Gb,_Gc,_Gd,_Ge,_Gf,_Gg,_Gh,_Gi,_Gj,_Gk,_Gl,_Gm,_Gn,_Go,_Gp,_Gq,_Gr,_Gs){if(_G5>=_Gh){if(_G5!=_Gh){return true;}else{if(_G6>=_Gi){if(_G6!=_Gi){return true;}else{if(_G7>=_Gj){if(_G7!=_Gj){return true;}else{if(_G8>=_Gk){if(_G8!=_Gk){return true;}else{if(_G9>=_Gl){if(_G9!=_Gl){return true;}else{if(_Ga>=_Gm){if(_Ga!=_Gm){return true;}else{if(_Gb>=_Gn){if(_Gb!=_Gn){return true;}else{if(_Gc>=_Go){if(_Gc!=_Go){return true;}else{if(_Gd>=_Gp){if(_Gd!=_Gp){return true;}else{if(_Ge>=_Gq){if(_Ge!=_Gq){return true;}else{var _Gt=E(_Gf),_Gu=E(_Gr);if(_Gt>=_Gu){if(_Gt!=_Gu){return true;}else{return new F(function(){return _bs(_Gg,_Gs);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_Gv=function(_Gw,_Gx){var _Gy=E(_Gw),_Gz=E(_Gy.a),_GA=E(_Gy.b),_GB=E(_Gy.c),_GC=E(_Gy.e),_GD=E(_Gx),_GE=E(_GD.a),_GF=E(_GD.b),_GG=E(_GD.c),_GH=E(_GD.e);return new F(function(){return _G4(_Gz.a,_Gz.b,_Gz.c,_GA.a,_GA.b,_GA.c,_GB.a,_GB.b,_GB.c,_Gy.d,_GC.a,_GC.b,_GE.a,_GE.b,_GE.c,_GF.a,_GF.b,_GF.c,_GG.a,_GG.b,_GG.c,_GD.d,_GH.a,_GH.b);});},_GI=function(_GJ,_GK,_GL,_GM,_GN,_GO){if(_GJ>=_GM){if(_GJ!=_GM){return true;}else{var _GP=E(_GK),_GQ=E(_GN),_GR=E(_GP.a),_GS=E(_GQ.a);if(_GR>=_GS){if(_GR!=_GS){return true;}else{var _GT=E(_GP.b),_GU=E(_GQ.b);if(_GT>=_GU){if(_GT!=_GU){return true;}else{var _GV=E(_GP.c),_GW=E(_GQ.c);if(_GV>=_GW){if(_GV!=_GW){return true;}else{return new F(function(){return _Gv(_GL,_GO);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_GX=function(_GY,_GZ){var _H0=E(_GY),_H1=E(_GZ);return new F(function(){return _GI(E(_H0.a),_H0.b,_H0.c,E(_H1.a),_H1.b,_H1.c);});},_H2=function(_H3,_H4){var _H5=E(_H3),_H6=E(_H5.a),_H7=E(_H4),_H8=E(_H7.a);if(_H6>=_H8){if(_H6!=_H8){return E(_H5);}else{var _H9=E(_H5.b),_Ha=E(_H7.b),_Hb=E(_H9.a),_Hc=E(_Ha.a);if(_Hb>=_Hc){if(_Hb!=_Hc){return E(_H5);}else{var _Hd=E(_H9.b),_He=E(_Ha.b);if(_Hd>=_He){if(_Hd!=_He){return E(_H5);}else{var _Hf=E(_H9.c),_Hg=E(_Ha.c);if(_Hf>=_Hg){if(_Hf!=_Hg){return E(_H5);}else{var _Hh=E(_H5.c),_Hi=_Hh.d,_Hj=E(_Hh.a),_Hk=_Hj.a,_Hl=_Hj.b,_Hm=_Hj.c,_Hn=E(_Hh.b),_Ho=_Hn.a,_Hp=_Hn.b,_Hq=_Hn.c,_Hr=E(_Hh.c),_Hs=_Hr.a,_Ht=_Hr.b,_Hu=_Hr.c,_Hv=E(_Hh.e),_Hw=E(_H7.c),_Hx=_Hw.d,_Hy=E(_Hw.a),_Hz=_Hy.a,_HA=_Hy.b,_HB=_Hy.c,_HC=E(_Hw.b),_HD=_HC.a,_HE=_HC.b,_HF=_HC.c,_HG=E(_Hw.c),_HH=_HG.a,_HI=_HG.b,_HJ=_HG.c,_HK=E(_Hw.e);if(_Hk>=_Hz){if(_Hk!=_Hz){return E(_H5);}else{if(_Hl>=_HA){if(_Hl!=_HA){return E(_H5);}else{if(_Hm>=_HB){if(_Hm!=_HB){return E(_H5);}else{if(_Ho>=_HD){if(_Ho!=_HD){return E(_H5);}else{if(_Hp>=_HE){if(_Hp!=_HE){return E(_H5);}else{if(_Hq>=_HF){if(_Hq!=_HF){return E(_H5);}else{if(_Hs>=_HH){if(_Hs!=_HH){return E(_H5);}else{if(_Ht>=_HI){if(_Ht!=_HI){return E(_H5);}else{if(_Hu>=_HJ){if(_Hu!=_HJ){return E(_H5);}else{if(_Hi>=_Hx){if(_Hi!=_Hx){return E(_H5);}else{var _HL=E(_Hv.a),_HM=E(_HK.a);return (_HL>=_HM)?(_HL!=_HM)?E(_H5):(E(_Hv.b)>E(_HK.b))?E(_H5):E(_H7):E(_H7);}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}},_HN=function(_HO,_HP){var _HQ=E(_HO),_HR=E(_HQ.a),_HS=E(_HP),_HT=E(_HS.a);if(_HR>=_HT){if(_HR!=_HT){return E(_HS);}else{var _HU=E(_HQ.b),_HV=E(_HS.b),_HW=E(_HU.a),_HX=E(_HV.a);if(_HW>=_HX){if(_HW!=_HX){return E(_HS);}else{var _HY=E(_HU.b),_HZ=E(_HV.b);if(_HY>=_HZ){if(_HY!=_HZ){return E(_HS);}else{var _I0=E(_HU.c),_I1=E(_HV.c);if(_I0>=_I1){if(_I0!=_I1){return E(_HS);}else{var _I2=E(_HQ.c),_I3=_I2.d,_I4=E(_I2.a),_I5=_I4.a,_I6=_I4.b,_I7=_I4.c,_I8=E(_I2.b),_I9=_I8.a,_Ia=_I8.b,_Ib=_I8.c,_Ic=E(_I2.c),_Id=_Ic.a,_Ie=_Ic.b,_If=_Ic.c,_Ig=E(_I2.e),_Ih=E(_HS.c),_Ii=_Ih.d,_Ij=E(_Ih.a),_Ik=_Ij.a,_Il=_Ij.b,_Im=_Ij.c,_In=E(_Ih.b),_Io=_In.a,_Ip=_In.b,_Iq=_In.c,_Ir=E(_Ih.c),_Is=_Ir.a,_It=_Ir.b,_Iu=_Ir.c,_Iv=E(_Ih.e);if(_I5>=_Ik){if(_I5!=_Ik){return E(_HS);}else{if(_I6>=_Il){if(_I6!=_Il){return E(_HS);}else{if(_I7>=_Im){if(_I7!=_Im){return E(_HS);}else{if(_I9>=_Io){if(_I9!=_Io){return E(_HS);}else{if(_Ia>=_Ip){if(_Ia!=_Ip){return E(_HS);}else{if(_Ib>=_Iq){if(_Ib!=_Iq){return E(_HS);}else{if(_Id>=_Is){if(_Id!=_Is){return E(_HS);}else{if(_Ie>=_It){if(_Ie!=_It){return E(_HS);}else{if(_If>=_Iu){if(_If!=_Iu){return E(_HS);}else{if(_I3>=_Ii){if(_I3!=_Ii){return E(_HS);}else{var _Iw=E(_Ig.a),_Ix=E(_Iv.a);return (_Iw>=_Ix)?(_Iw!=_Ix)?E(_HS):(E(_Ig.b)>E(_Iv.b))?E(_HS):E(_HQ):E(_HQ);}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}},_Iy={_:0,a:_Cb,b:_D5,c:_E3,d:_F1,e:_FZ,f:_GX,g:_H2,h:_HN},_Iz=function(_IA,_IB,_IC,_ID){var _IE=E(_ID);if(!_IE._){var _IF=_IE.c,_IG=_IE.d,_IH=_IE.e,_II=E(_IE.b),_IJ=E(_II.a);if(_IA>=_IJ){if(_IA!=_IJ){return new F(function(){return _xc(_II,_IF,_IG,B(_Iz(_IA,_IB,_IC,_IH)));});}else{var _IK=E(_II.b);if(_IB>=_IK){if(_IB!=_IK){return new F(function(){return _xc(_II,_IF,_IG,B(_Iz(_IA,_IB,_IC,_IH)));});}else{return new T5(0,_IE.a,E(new T2(0,_IA,_IB)),_IC,E(_IG),E(_IH));}}else{return new F(function(){return _wv(_II,_IF,B(_Iz(_IA,_IB,_IC,_IG)),_IH);});}}}else{return new F(function(){return _wv(_II,_IF,B(_Iz(_IA,_IB,_IC,_IG)),_IH);});}}else{return new T5(0,1,E(new T2(0,_IA,_IB)),_IC,E(_wq),E(_wq));}},_IL=new T0(1),_IM=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_IN=function(_IO){return new F(function(){return err(_IM);});},_IP=new T(function(){return B(_IN(_));}),_IQ=function(_IR,_IS,_IT){var _IU=E(_IT);if(!_IU._){var _IV=_IU.a,_IW=E(_IS);if(!_IW._){var _IX=_IW.a,_IY=_IW.b;if(_IX<=(imul(3,_IV)|0)){return new T4(0,(1+_IX|0)+_IV|0,E(_IR),E(_IW),E(_IU));}else{var _IZ=E(_IW.c);if(!_IZ._){var _J0=_IZ.a,_J1=E(_IW.d);if(!_J1._){var _J2=_J1.a,_J3=_J1.b,_J4=_J1.c;if(_J2>=(imul(2,_J0)|0)){var _J5=function(_J6){var _J7=E(_J1.d);return (_J7._==0)?new T4(0,(1+_IX|0)+_IV|0,E(_J3),E(new T4(0,(1+_J0|0)+_J6|0,E(_IY),E(_IZ),E(_J4))),E(new T4(0,(1+_IV|0)+_J7.a|0,E(_IR),E(_J7),E(_IU)))):new T4(0,(1+_IX|0)+_IV|0,E(_J3),E(new T4(0,(1+_J0|0)+_J6|0,E(_IY),E(_IZ),E(_J4))),E(new T4(0,1+_IV|0,E(_IR),E(_IL),E(_IU))));},_J8=E(_J4);if(!_J8._){return new F(function(){return _J5(_J8.a);});}else{return new F(function(){return _J5(0);});}}else{return new T4(0,(1+_IX|0)+_IV|0,E(_IY),E(_IZ),E(new T4(0,(1+_IV|0)+_J2|0,E(_IR),E(_J1),E(_IU))));}}else{return E(_IP);}}else{return E(_IP);}}}else{return new T4(0,1+_IV|0,E(_IR),E(_IL),E(_IU));}}else{var _J9=E(_IS);if(!_J9._){var _Ja=_J9.a,_Jb=_J9.b,_Jc=_J9.d,_Jd=E(_J9.c);if(!_Jd._){var _Je=_Jd.a,_Jf=E(_Jc);if(!_Jf._){var _Jg=_Jf.a,_Jh=_Jf.b,_Ji=_Jf.c;if(_Jg>=(imul(2,_Je)|0)){var _Jj=function(_Jk){var _Jl=E(_Jf.d);return (_Jl._==0)?new T4(0,1+_Ja|0,E(_Jh),E(new T4(0,(1+_Je|0)+_Jk|0,E(_Jb),E(_Jd),E(_Ji))),E(new T4(0,1+_Jl.a|0,E(_IR),E(_Jl),E(_IL)))):new T4(0,1+_Ja|0,E(_Jh),E(new T4(0,(1+_Je|0)+_Jk|0,E(_Jb),E(_Jd),E(_Ji))),E(new T4(0,1,E(_IR),E(_IL),E(_IL))));},_Jm=E(_Ji);if(!_Jm._){return new F(function(){return _Jj(_Jm.a);});}else{return new F(function(){return _Jj(0);});}}else{return new T4(0,1+_Ja|0,E(_Jb),E(_Jd),E(new T4(0,1+_Jg|0,E(_IR),E(_Jf),E(_IL))));}}else{return new T4(0,3,E(_Jb),E(_Jd),E(new T4(0,1,E(_IR),E(_IL),E(_IL))));}}else{var _Jn=E(_Jc);return (_Jn._==0)?new T4(0,3,E(_Jn.b),E(new T4(0,1,E(_Jb),E(_IL),E(_IL))),E(new T4(0,1,E(_IR),E(_IL),E(_IL)))):new T4(0,2,E(_IR),E(_J9),E(_IL));}}else{return new T4(0,1,E(_IR),E(_IL),E(_IL));}}},_Jo=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Jp=function(_Jq){return new F(function(){return err(_Jo);});},_Jr=new T(function(){return B(_Jp(_));}),_Js=function(_Jt,_Ju,_Jv){var _Jw=E(_Ju);if(!_Jw._){var _Jx=_Jw.a,_Jy=E(_Jv);if(!_Jy._){var _Jz=_Jy.a,_JA=_Jy.b;if(_Jz<=(imul(3,_Jx)|0)){return new T4(0,(1+_Jx|0)+_Jz|0,E(_Jt),E(_Jw),E(_Jy));}else{var _JB=E(_Jy.c);if(!_JB._){var _JC=_JB.a,_JD=_JB.b,_JE=_JB.c,_JF=E(_Jy.d);if(!_JF._){var _JG=_JF.a;if(_JC>=(imul(2,_JG)|0)){var _JH=function(_JI){var _JJ=E(_Jt),_JK=E(_JB.d);return (_JK._==0)?new T4(0,(1+_Jx|0)+_Jz|0,E(_JD),E(new T4(0,(1+_Jx|0)+_JI|0,E(_JJ),E(_Jw),E(_JE))),E(new T4(0,(1+_JG|0)+_JK.a|0,E(_JA),E(_JK),E(_JF)))):new T4(0,(1+_Jx|0)+_Jz|0,E(_JD),E(new T4(0,(1+_Jx|0)+_JI|0,E(_JJ),E(_Jw),E(_JE))),E(new T4(0,1+_JG|0,E(_JA),E(_IL),E(_JF))));},_JL=E(_JE);if(!_JL._){return new F(function(){return _JH(_JL.a);});}else{return new F(function(){return _JH(0);});}}else{return new T4(0,(1+_Jx|0)+_Jz|0,E(_JA),E(new T4(0,(1+_Jx|0)+_JC|0,E(_Jt),E(_Jw),E(_JB))),E(_JF));}}else{return E(_Jr);}}else{return E(_Jr);}}}else{return new T4(0,1+_Jx|0,E(_Jt),E(_Jw),E(_IL));}}else{var _JM=E(_Jv);if(!_JM._){var _JN=_JM.a,_JO=_JM.b,_JP=_JM.d,_JQ=E(_JM.c);if(!_JQ._){var _JR=_JQ.a,_JS=_JQ.b,_JT=_JQ.c,_JU=E(_JP);if(!_JU._){var _JV=_JU.a;if(_JR>=(imul(2,_JV)|0)){var _JW=function(_JX){var _JY=E(_Jt),_JZ=E(_JQ.d);return (_JZ._==0)?new T4(0,1+_JN|0,E(_JS),E(new T4(0,1+_JX|0,E(_JY),E(_IL),E(_JT))),E(new T4(0,(1+_JV|0)+_JZ.a|0,E(_JO),E(_JZ),E(_JU)))):new T4(0,1+_JN|0,E(_JS),E(new T4(0,1+_JX|0,E(_JY),E(_IL),E(_JT))),E(new T4(0,1+_JV|0,E(_JO),E(_IL),E(_JU))));},_K0=E(_JT);if(!_K0._){return new F(function(){return _JW(_K0.a);});}else{return new F(function(){return _JW(0);});}}else{return new T4(0,1+_JN|0,E(_JO),E(new T4(0,1+_JR|0,E(_Jt),E(_IL),E(_JQ))),E(_JU));}}else{return new T4(0,3,E(_JS),E(new T4(0,1,E(_Jt),E(_IL),E(_IL))),E(new T4(0,1,E(_JO),E(_IL),E(_IL))));}}else{var _K1=E(_JP);return (_K1._==0)?new T4(0,3,E(_JO),E(new T4(0,1,E(_Jt),E(_IL),E(_IL))),E(_K1)):new T4(0,2,E(_Jt),E(_IL),E(_JM));}}else{return new T4(0,1,E(_Jt),E(_IL),E(_IL));}}},_K2=function(_K3,_K4,_K5){var _K6=E(_K4),_K7=E(_K5);if(!_K7._){var _K8=_K7.b,_K9=_K7.c,_Ka=_K7.d;switch(B(A3(_wo,_K3,_K6,_K8))){case 0:return new F(function(){return _IQ(_K8,B(_K2(_K3,_K6,_K9)),_Ka);});break;case 1:return new T4(0,_K7.a,E(_K6),E(_K9),E(_Ka));default:return new F(function(){return _Js(_K8,_K9,B(_K2(_K3,_K6,_Ka)));});}}else{return new T4(0,1,E(_K6),E(_IL),E(_IL));}},_Kb=function(_Kc,_Kd,_Ke,_Kf,_Kg){var _Kh=E(_Kg);if(!_Kh._){var _Ki=new T(function(){var _Kj=B(_Kb(_Kh.a,_Kh.b,_Kh.c,_Kh.d,_Kh.e));return new T2(0,_Kj.a,_Kj.b);});return new T2(0,new T(function(){return E(E(_Ki).a);}),new T(function(){return B(_wv(_Kd,_Ke,_Kf,E(_Ki).b));}));}else{return new T2(0,new T2(0,_Kd,_Ke),_Kf);}},_Kk=function(_Kl,_Km,_Kn,_Ko,_Kp){var _Kq=E(_Ko);if(!_Kq._){var _Kr=new T(function(){var _Ks=B(_Kk(_Kq.a,_Kq.b,_Kq.c,_Kq.d,_Kq.e));return new T2(0,_Ks.a,_Ks.b);});return new T2(0,new T(function(){return E(E(_Kr).a);}),new T(function(){return B(_xc(_Km,_Kn,E(_Kr).b,_Kp));}));}else{return new T2(0,new T2(0,_Km,_Kn),_Kp);}},_Kt=function(_Ku,_Kv){var _Kw=E(_Ku);if(!_Kw._){var _Kx=_Kw.a,_Ky=E(_Kv);if(!_Ky._){var _Kz=_Ky.a;if(_Kx<=_Kz){var _KA=B(_Kk(_Kz,_Ky.b,_Ky.c,_Ky.d,_Ky.e)),_KB=E(_KA.a);return new F(function(){return _wv(_KB.a,_KB.b,_Kw,_KA.b);});}else{var _KC=B(_Kb(_Kx,_Kw.b,_Kw.c,_Kw.d,_Kw.e)),_KD=E(_KC.a);return new F(function(){return _xc(_KD.a,_KD.b,_KC.b,_Ky);});}}else{return E(_Kw);}}else{return E(_Kv);}},_KE=function(_KF,_KG,_KH,_KI){var _KJ=E(_KI);if(!_KJ._){var _KK=_KJ.c,_KL=_KJ.d,_KM=_KJ.e,_KN=E(_KJ.b),_KO=E(_KN.a);if(_KG>=_KO){if(_KG!=_KO){return new F(function(){return _wv(_KN,_KK,_KL,B(_KE(_KF,_KG,_KH,_KM)));});}else{var _KP=E(_KN.b);if(_KH>=_KP){if(_KH!=_KP){return new F(function(){return _wv(_KN,_KK,_KL,B(_KE(_KF,_KG,_KH,_KM)));});}else{var _KQ=B(A2(_KF,_KN,_KK));if(!_KQ._){return new F(function(){return _Kt(_KL,_KM);});}else{return new T5(0,_KJ.a,E(_KN),_KQ.a,E(_KL),E(_KM));}}}else{return new F(function(){return _xc(_KN,_KK,B(_KE(_KF,_KG,_KH,_KL)),_KM);});}}}else{return new F(function(){return _xc(_KN,_KK,B(_KE(_KF,_KG,_KH,_KL)),_KM);});}}else{return new T0(1);}},_KR=function(_KS,_KT,_KU,_KV){var _KW=E(_KV);if(!_KW._){var _KX=_KW.c,_KY=_KW.d,_KZ=_KW.e,_L0=E(_KW.b),_L1=E(_L0.a);if(_KT>=_L1){if(_KT!=_L1){return new F(function(){return _wv(_L0,_KX,_KY,B(_KR(_KS,_KT,_KU,_KZ)));});}else{var _L2=E(_KU),_L3=E(_L0.b);if(_L2>=_L3){if(_L2!=_L3){return new F(function(){return _wv(_L0,_KX,_KY,B(_KE(_KS,_KT,_L2,_KZ)));});}else{var _L4=B(A2(_KS,_L0,_KX));if(!_L4._){return new F(function(){return _Kt(_KY,_KZ);});}else{return new T5(0,_KW.a,E(_L0),_L4.a,E(_KY),E(_KZ));}}}else{return new F(function(){return _xc(_L0,_KX,B(_KE(_KS,_KT,_L2,_KY)),_KZ);});}}}else{return new F(function(){return _xc(_L0,_KX,B(_KR(_KS,_KT,_KU,_KY)),_KZ);});}}else{return new T0(1);}},_L5=function(_L6,_L7,_L8,_L9){var _La=E(_L9);if(!_La._){var _Lb=_La.c,_Lc=_La.d,_Ld=_La.e,_Le=E(_La.b),_Lf=E(_L7),_Lg=E(_Le.a);if(_Lf>=_Lg){if(_Lf!=_Lg){return new F(function(){return _wv(_Le,_Lb,_Lc,B(_KR(_L6,_Lf,_L8,_Ld)));});}else{var _Lh=E(_L8),_Li=E(_Le.b);if(_Lh>=_Li){if(_Lh!=_Li){return new F(function(){return _wv(_Le,_Lb,_Lc,B(_KE(_L6,_Lf,_Lh,_Ld)));});}else{var _Lj=B(A2(_L6,_Le,_Lb));if(!_Lj._){return new F(function(){return _Kt(_Lc,_Ld);});}else{return new T5(0,_La.a,E(_Le),_Lj.a,E(_Lc),E(_Ld));}}}else{return new F(function(){return _xc(_Le,_Lb,B(_KE(_L6,_Lf,_Lh,_Lc)),_Ld);});}}}else{return new F(function(){return _xc(_Le,_Lb,B(_KR(_L6,_Lf,_L8,_Lc)),_Ld);});}}else{return new T0(1);}},_Lk=function(_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu){var _Lv=_Lt-_Ln,_Lw=_Lu-_Lo,_Lx=_Lq-_Ln,_Ly=_Lr-_Lo,_Lz=_Lx*_Lw-_Ly*_Lv+(_Lx*_Lw-_Ly*_Lv);return (_Lz>0)?new T1(1,new T(function(){var _LA=_Lv*_Lv+_Lw*_Lw,_LB=_Lx*_Lx+_Ly*_Ly,_LC=E(_Ll),_LD=_Ln+(_Lw*_LB-_Ly*_LA)/_Lz,_LE=_Lo+(_Lx*_LA-_Lv*_LB)/_Lz,_LF=_LE+Math.sqrt((_LD-_Ln)*(_LD-_Ln)+(_LE-_Lo)*(_LE-_Lo));if(_LF>_LC){return new T5(0,E(new T3(0,_Lm,_Ln,_Lo)),E(new T3(0,_Lp,_Lq,_Lr)),E(new T3(0,_Ls,_Lt,_Lu)),_LC,E(new T2(0,_LD,_LE)));}else{return new T5(0,E(new T3(0,_Lm,_Ln,_Lo)),E(new T3(0,_Lp,_Lq,_Lr)),E(new T3(0,_Ls,_Lt,_Lu)),_LF,E(new T2(0,_LD,_LE)));}})):__Z;},_LG=function(_LH,_LI,_LJ){while(1){var _LK=E(_LH);if(!_LK._){return E(_LI);}else{_LH=_LK.a;_LI=_LK.b;_LJ=_LK.c;continue;}}},_LL=function(_LM,_LN,_LO){var _LP=E(_LM);return (_LP._==0)?E(_LO):new T3(1,new T(function(){return B(_LL(_LP.a,_LP.b,_LP.c));}),_LN,_LO);},_LQ=new T(function(){return B(_7Z("Fortune/BreakpointTree.hs:(154,1)-(163,30)|function delete"));}),_LR=new T(function(){return B(unCStr("delete: Reached Nil"));}),_LS=new T(function(){return B(err(_LR));}),_LT=function(_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1){var _M2=E(_M1);if(!_M2._){return E(_LS);}else{var _M3=_M2.a,_M4=_M2.c,_M5=E(_M2.b),_M6=E(_M5.a),_M7=_M6.b,_M8=_M6.c,_M9=E(_M5.b),_Ma=_M9.b,_Mb=_M9.c,_Mc=function(_Md){var _Me=_LW-_LZ,_Mf=function(_Mg){var _Mh=_M8-_Mb,_Mi=function(_Mj){return (_Mg>=_Mj)?(_Mg<_Mj)?E(_LQ):new T3(1,_M3,_M5,new T(function(){return B(_LT(_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M4));})):new T3(1,new T(function(){return B(_LT(_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M3));}),_M5,_M4);};if(_Mh!=0){if(_Mh<=0){if( -_Mh>=1.0e-7){var _Mk=E(_M0);return new F(function(){return _Mi((_M8*_Ma+Math.sqrt(((_M7-_Ma)*(_M7-_Ma)+_Mh*_Mh)*(_M8-_Mk)*(_Mb-_Mk))+(_M7*(_Mk-_Mb)-_Ma*_Mk))/_Mh);});}else{return new F(function(){return _Mi((_M7+_Ma)/2);});}}else{if(_Mh>=1.0e-7){var _Ml=E(_M0);return new F(function(){return _Mi((_M8*_Ma+Math.sqrt(((_M7-_Ma)*(_M7-_Ma)+_Mh*_Mh)*(_M8-_Ml)*(_Mb-_Ml))+(_M7*(_Ml-_Mb)-_Ma*_Ml))/_Mh);});}else{return new F(function(){return _Mi((_M7+_Ma)/2);});}}}else{return new F(function(){return _Mi((_M7+_Ma)/2);});}};if(_Me!=0){if(_Me<=0){if( -_Me>=1.0e-7){var _Mm=E(_M0);return new F(function(){return _Mf((_LW*_LY+Math.sqrt(((_LV-_LY)*(_LV-_LY)+_Me*_Me)*(_LW-_Mm)*(_LZ-_Mm))+(_LV*(_Mm-_LZ)-_LY*_Mm))/_Me);});}else{return new F(function(){return _Mf((_LV+_LY)/2);});}}else{if(_Me>=1.0e-7){var _Mn=E(_M0);return new F(function(){return _Mf((_LW*_LY+Math.sqrt(((_LV-_LY)*(_LV-_LY)+_Me*_Me)*(_LW-_Mn)*(_LZ-_Mn))+(_LV*(_Mn-_LZ)-_LY*_Mn))/_Me);});}else{return new F(function(){return _Mf((_LV+_LY)/2);});}}}else{return new F(function(){return _Mf((_LV+_LY)/2);});}};if(_M6.a!=_LU){return new F(function(){return _Mc(_);});}else{if(_M9.a!=_LX){return new F(function(){return _Mc(_);});}else{var _Mo=E(_M3);if(!_Mo._){return E(_M4);}else{var _Mp=E(_M4);if(!_Mp._){return E(_Mo);}else{var _Mq=_Mp.a,_Mr=_Mp.b,_Ms=_Mp.c;return new T3(1,_Mo,new T(function(){return B(_LG(_Mq,_Mr,_Ms));}),new T(function(){return B(_LL(_Mq,_Mr,_Ms));}));}}}}}},_Mt=function(_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB,_MC,_MD){var _ME=E(_MC),_MF=E(_ME.a),_MG=_MF.b,_MH=_MF.c,_MI=E(_ME.b),_MJ=_MI.b,_MK=_MI.c,_ML=function(_MM){var _MN=_Mw-_Mz,_MO=function(_MP){var _MQ=_MH-_MK,_MR=function(_MS){return (_MP>=_MS)?(_MP<_MS)?E(_LQ):new T3(1,_MB,_ME,new T(function(){return B(_LT(_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MD));})):new T3(1,new T(function(){return B(_LT(_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB));}),_ME,_MD);};if(_MQ!=0){if(_MQ<=0){if( -_MQ>=1.0e-7){var _MT=E(_MA);return new F(function(){return _MR((_MH*_MJ+Math.sqrt(((_MG-_MJ)*(_MG-_MJ)+_MQ*_MQ)*(_MH-_MT)*(_MK-_MT))+(_MG*(_MT-_MK)-_MJ*_MT))/_MQ);});}else{return new F(function(){return _MR((_MG+_MJ)/2);});}}else{if(_MQ>=1.0e-7){var _MU=E(_MA);return new F(function(){return _MR((_MH*_MJ+Math.sqrt(((_MG-_MJ)*(_MG-_MJ)+_MQ*_MQ)*(_MH-_MU)*(_MK-_MU))+(_MG*(_MU-_MK)-_MJ*_MU))/_MQ);});}else{return new F(function(){return _MR((_MG+_MJ)/2);});}}}else{return new F(function(){return _MR((_MG+_MJ)/2);});}};if(_MN!=0){if(_MN<=0){if( -_MN>=1.0e-7){var _MV=E(_MA);return new F(function(){return _MO((_Mw*_My+Math.sqrt(((_Mv-_My)*(_Mv-_My)+_MN*_MN)*(_Mw-_MV)*(_Mz-_MV))+(_Mv*(_MV-_Mz)-_My*_MV))/_MN);});}else{return new F(function(){return _MO((_Mv+_My)/2);});}}else{if(_MN>=1.0e-7){var _MW=E(_MA);return new F(function(){return _MO((_Mw*_My+Math.sqrt(((_Mv-_My)*(_Mv-_My)+_MN*_MN)*(_Mw-_MW)*(_Mz-_MW))+(_Mv*(_MW-_Mz)-_My*_MW))/_MN);});}else{return new F(function(){return _MO((_Mv+_My)/2);});}}}else{return new F(function(){return _MO((_Mv+_My)/2);});}};if(_MF.a!=_Mu){return new F(function(){return _ML(_);});}else{if(_MI.a!=_Mx){return new F(function(){return _ML(_);});}else{var _MX=E(_MB);if(!_MX._){return E(_MD);}else{var _MY=E(_MD);if(!_MY._){return E(_MX);}else{var _MZ=_MY.a,_N0=_MY.b,_N1=_MY.c;return new T3(1,_MX,new T(function(){return B(_LG(_MZ,_N0,_N1));}),new T(function(){return B(_LL(_MZ,_N0,_N1));}));}}}}},_N2=function(_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne){var _Nf=E(_Nd),_Ng=E(_Nf.a),_Nh=_Ng.b,_Ni=_Ng.c,_Nj=E(_Nf.b),_Nk=_Nj.b,_Nl=_Nj.c,_Nm=function(_Nn){var _No=_N5-_N8,_Np=function(_Nq){var _Nr=_Ni-_Nl,_Ns=function(_Nt){return (_Nq>=_Nt)?(_Nq<_Nt)?E(_LQ):new T3(1,new T3(1,_Na,_Nb,_Nc),_Nf,new T(function(){return B(_LT(_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Ne));})):new T3(1,new T(function(){return B(_Mt(_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc));}),_Nf,_Ne);};if(_Nr!=0){if(_Nr<=0){if( -_Nr>=1.0e-7){var _Nu=E(_N9);return new F(function(){return _Ns((_Ni*_Nk+Math.sqrt(((_Nh-_Nk)*(_Nh-_Nk)+_Nr*_Nr)*(_Ni-_Nu)*(_Nl-_Nu))+(_Nh*(_Nu-_Nl)-_Nk*_Nu))/_Nr);});}else{return new F(function(){return _Ns((_Nh+_Nk)/2);});}}else{if(_Nr>=1.0e-7){var _Nv=E(_N9);return new F(function(){return _Ns((_Ni*_Nk+Math.sqrt(((_Nh-_Nk)*(_Nh-_Nk)+_Nr*_Nr)*(_Ni-_Nv)*(_Nl-_Nv))+(_Nh*(_Nv-_Nl)-_Nk*_Nv))/_Nr);});}else{return new F(function(){return _Ns((_Nh+_Nk)/2);});}}}else{return new F(function(){return _Ns((_Nh+_Nk)/2);});}};if(_No!=0){if(_No<=0){if( -_No>=1.0e-7){var _Nw=E(_N9);return new F(function(){return _Np((_N5*_N7+Math.sqrt(((_N4-_N7)*(_N4-_N7)+_No*_No)*(_N5-_Nw)*(_N8-_Nw))+(_N4*(_Nw-_N8)-_N7*_Nw))/_No);});}else{return new F(function(){return _Np((_N4+_N7)/2);});}}else{if(_No>=1.0e-7){var _Nx=E(_N9);return new F(function(){return _Np((_N5*_N7+Math.sqrt(((_N4-_N7)*(_N4-_N7)+_No*_No)*(_N5-_Nx)*(_N8-_Nx))+(_N4*(_Nx-_N8)-_N7*_Nx))/_No);});}else{return new F(function(){return _Np((_N4+_N7)/2);});}}}else{return new F(function(){return _Np((_N4+_N7)/2);});}};if(_Ng.a!=_N3){return new F(function(){return _Nm(_);});}else{if(_Nj.a!=_N6){return new F(function(){return _Nm(_);});}else{var _Ny=E(_Ne);if(!_Ny._){return new T3(1,_Na,_Nb,_Nc);}else{var _Nz=_Ny.a,_NA=_Ny.b,_NB=_Ny.c;return new T3(1,new T3(1,_Na,_Nb,_Nc),new T(function(){return B(_LG(_Nz,_NA,_NB));}),new T(function(){return B(_LL(_Nz,_NA,_NB));}));}}}},_NC=function(_ND,_NE,_NF,_NG,_NH){var _NI=_NE-_NG;if(_NI!=0){if(_NI<=0){if( -_NI>=1.0e-7){var _NJ=E(_NH);return (_NE*_NF+Math.sqrt(((_ND-_NF)*(_ND-_NF)+_NI*_NI)*(_NE-_NJ)*(_NG-_NJ))+(_ND*(_NJ-_NG)-_NF*_NJ))/_NI;}else{return (_ND+_NF)/2;}}else{if(_NI>=1.0e-7){var _NK=E(_NH);return (_NE*_NF+Math.sqrt(((_ND-_NF)*(_ND-_NF)+_NI*_NI)*(_NE-_NK)*(_NG-_NK))+(_ND*(_NK-_NG)-_NF*_NK))/_NI;}else{return (_ND+_NF)/2;}}}else{return (_ND+_NF)/2;}},_NL=new T(function(){return B(unCStr("delete2: reached nil."));}),_NM=new T(function(){return B(err(_NL));}),_NN=function(_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1){var _O2=E(_O1);if(!_O2._){return E(_NM);}else{var _O3=_O2.a,_O4=_O2.c,_O5=E(_O2.b),_O6=E(_O5.a),_O7=_O6.a,_O8=_O6.b,_O9=_O6.c,_Oa=E(_O5.b),_Ob=_Oa.a,_Oc=_Oa.b,_Od=_Oa.c,_Oe=function(_Of){var _Og=function(_Oh){var _Oi=_NQ-_NT,_Oj=function(_Ok){var _Ol=_O9-_Od,_Om=function(_On){var _Oo=new T(function(){return B(_NC(_NV,_NW,_NY,_NZ,_O0));}),_Op=function(_Oq){var _Or=function(_Os){return (_Ok>=_On)?new T3(1,new T(function(){return B(_LT(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O3));}),_O5,new T(function(){return B(_LT(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_O4));})):new T3(1,new T(function(){return B(_LT(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_O3));}),_O5,new T(function(){return B(_LT(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O4));}));};if(_Ok<_On){return new F(function(){return _Or(_);});}else{if(E(_Oo)<_On){return new F(function(){return _Or(_);});}else{return new T3(1,_O3,_O5,new T(function(){return B(_NN(_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O4));}));}}};if(_Ok>=_On){return new F(function(){return _Op(_);});}else{if(E(_Oo)>=_On){return new F(function(){return _Op(_);});}else{return new T3(1,new T(function(){return B(_NN(_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O3));}),_O5,_O4);}}};if(_Ol!=0){if(_Ol<=0){if( -_Ol>=1.0e-7){var _Ot=E(_O0);return new F(function(){return _Om((_O9*_Oc+Math.sqrt(((_O8-_Oc)*(_O8-_Oc)+_Ol*_Ol)*(_O9-_Ot)*(_Od-_Ot))+(_O8*(_Ot-_Od)-_Oc*_Ot))/_Ol);});}else{return new F(function(){return _Om((_O8+_Oc)/2);});}}else{if(_Ol>=1.0e-7){var _Ou=E(_O0);return new F(function(){return _Om((_O9*_Oc+Math.sqrt(((_O8-_Oc)*(_O8-_Oc)+_Ol*_Ol)*(_O9-_Ou)*(_Od-_Ou))+(_O8*(_Ou-_Od)-_Oc*_Ou))/_Ol);});}else{return new F(function(){return _Om((_O8+_Oc)/2);});}}}else{return new F(function(){return _Om((_O8+_Oc)/2);});}};if(_Oi!=0){if(_Oi<=0){if( -_Oi>=1.0e-7){var _Ov=E(_O0);return new F(function(){return _Oj((_NQ*_NS+Math.sqrt(((_NP-_NS)*(_NP-_NS)+_Oi*_Oi)*(_NQ-_Ov)*(_NT-_Ov))+(_NP*(_Ov-_NT)-_NS*_Ov))/_Oi);});}else{return new F(function(){return _Oj((_NP+_NS)/2);});}}else{if(_Oi>=1.0e-7){var _Ow=E(_O0);return new F(function(){return _Oj((_NQ*_NS+Math.sqrt(((_NP-_NS)*(_NP-_NS)+_Oi*_Oi)*(_NQ-_Ow)*(_NT-_Ow))+(_NP*(_Ow-_NT)-_NS*_Ow))/_Oi);});}else{return new F(function(){return _Oj((_NP+_NS)/2);});}}}else{return new F(function(){return _Oj((_NP+_NS)/2);});}};if(_NU!=_O7){return new F(function(){return _Og(_);});}else{if(_NX!=_Ob){return new F(function(){return _Og(_);});}else{var _Ox=E(_O3);if(!_Ox._){return new F(function(){return _LT(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_O4);});}else{var _Oy=_Ox.a,_Oz=_Ox.b,_OA=_Ox.c,_OB=E(_O4);if(!_OB._){return new F(function(){return _Mt(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_Oy,_Oz,_OA);});}else{var _OC=_OB.a,_OD=_OB.b,_OE=_OB.c;return new F(function(){return _N2(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_Oy,_Oz,_OA,new T(function(){return B(_LG(_OC,_OD,_OE));}),new T(function(){return B(_LL(_OC,_OD,_OE));}));});}}}}};if(_NO!=_O7){return new F(function(){return _Oe(_);});}else{if(_NR!=_Ob){return new F(function(){return _Oe(_);});}else{var _OF=E(_O3);if(!_OF._){return new F(function(){return _LT(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O4);});}else{var _OG=_OF.a,_OH=_OF.b,_OI=_OF.c,_OJ=E(_O4);if(!_OJ._){return new F(function(){return _Mt(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_OG,_OH,_OI);});}else{var _OK=_OJ.a,_OL=_OJ.b,_OM=_OJ.c;return new F(function(){return _N2(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_OG,_OH,_OI,new T(function(){return B(_LG(_OK,_OL,_OM));}),new T(function(){return B(_LL(_OK,_OL,_OM));}));});}}}}}},_ON=__Z,_OO=new T(function(){return B(unCStr("insertPar: Cannot insert into empty tree."));}),_OP=new T(function(){return B(err(_OO));}),_OQ=function(_OR,_OS,_OT,_OU,_OV){var _OW=E(_OV);if(!_OW._){return E(_OP);}else{var _OX=_OW.b,_OY=_OW.c,_OZ=new T3(0,_OR,_OS,_OT),_P0=E(_OW.a);if(!_P0._){var _P1=E(_OY);if(!_P1._){var _P2=E(_OX),_P3=E(_P2.a),_P4=_P3.b,_P5=_P3.c,_P6=E(_P2.b),_P7=_P6.b,_P8=_P6.c,_P9=_P5-_P8,_Pa=function(_Pb){return (_OS>=_Pb)?new T2(0,new T3(1,_ON,_P2,new T3(1,_ON,new T2(0,E(_P6),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_P6)),_ON))),new T1(1,_P2)):new T2(0,new T3(1,new T3(1,_ON,new T2(0,E(_P3),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_P3)),_ON)),_P2,_ON),new T1(0,_P2));};if(_P9!=0){if(_P9<=0){if( -_P9>=1.0e-7){var _Pc=E(_OU);return new F(function(){return _Pa((_P5*_P7+Math.sqrt(((_P4-_P7)*(_P4-_P7)+_P9*_P9)*(_P5-_Pc)*(_P8-_Pc))+(_P4*(_Pc-_P8)-_P7*_Pc))/_P9);});}else{return new F(function(){return _Pa((_P4+_P7)/2);});}}else{if(_P9>=1.0e-7){var _Pd=E(_OU);return new F(function(){return _Pa((_P5*_P7+Math.sqrt(((_P4-_P7)*(_P4-_P7)+_P9*_P9)*(_P5-_Pd)*(_P8-_Pd))+(_P4*(_Pd-_P8)-_P7*_Pd))/_P9);});}else{return new F(function(){return _Pa((_P4+_P7)/2);});}}}else{return new F(function(){return _Pa((_P4+_P7)/2);});}}else{var _Pe=E(_OX),_Pf=E(_Pe.a),_Pg=_Pf.b,_Ph=_Pf.c,_Pi=E(_Pe.b),_Pj=_Pi.b,_Pk=_Pi.c,_Pl=_Ph-_Pk,_Pm=function(_Pn){if(_OS>=_Pn){var _Po=new T(function(){var _Pp=B(_OQ(_OR,_OS,_OT,_OU,_P1));return new T2(0,_Pp.a,_Pp.b);});return new T2(0,new T3(1,_ON,_Pe,new T(function(){return E(E(_Po).a);})),new T(function(){return E(E(_Po).b);}));}else{return new T2(0,new T3(1,new T3(1,_ON,new T2(0,E(_Pf),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_Pf)),_ON)),_Pe,_P1),new T1(0,_Pe));}};if(_Pl!=0){if(_Pl<=0){if( -_Pl>=1.0e-7){var _Pq=E(_OU);return new F(function(){return _Pm((_Ph*_Pj+Math.sqrt(((_Pg-_Pj)*(_Pg-_Pj)+_Pl*_Pl)*(_Ph-_Pq)*(_Pk-_Pq))+(_Pg*(_Pq-_Pk)-_Pj*_Pq))/_Pl);});}else{return new F(function(){return _Pm((_Pg+_Pj)/2);});}}else{if(_Pl>=1.0e-7){var _Pr=E(_OU);return new F(function(){return _Pm((_Ph*_Pj+Math.sqrt(((_Pg-_Pj)*(_Pg-_Pj)+_Pl*_Pl)*(_Ph-_Pr)*(_Pk-_Pr))+(_Pg*(_Pr-_Pk)-_Pj*_Pr))/_Pl);});}else{return new F(function(){return _Pm((_Pg+_Pj)/2);});}}}else{return new F(function(){return _Pm((_Pg+_Pj)/2);});}}}else{var _Ps=E(_OY);if(!_Ps._){var _Pt=E(_OX),_Pu=E(_Pt.b),_Pv=_Pu.b,_Pw=_Pu.c,_Px=E(_Pt.a),_Py=_Px.b,_Pz=_Px.c,_PA=_Pz-_Pw,_PB=function(_PC){if(_OS>=_PC){return new T2(0,new T3(1,_P0,_Pt,new T3(1,_ON,new T2(0,E(_Pu),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_Pu)),_ON))),new T1(1,_Pt));}else{var _PD=new T(function(){var _PE=B(_OQ(_OR,_OS,_OT,_OU,_P0));return new T2(0,_PE.a,_PE.b);});return new T2(0,new T3(1,new T(function(){return E(E(_PD).a);}),_Pt,_ON),new T(function(){return E(E(_PD).b);}));}};if(_PA!=0){if(_PA<=0){if( -_PA>=1.0e-7){var _PF=E(_OU);return new F(function(){return _PB((_Pz*_Pv+Math.sqrt(((_Py-_Pv)*(_Py-_Pv)+_PA*_PA)*(_Pz-_PF)*(_Pw-_PF))+(_Py*(_PF-_Pw)-_Pv*_PF))/_PA);});}else{return new F(function(){return _PB((_Py+_Pv)/2);});}}else{if(_PA>=1.0e-7){var _PG=E(_OU);return new F(function(){return _PB((_Pz*_Pv+Math.sqrt(((_Py-_Pv)*(_Py-_Pv)+_PA*_PA)*(_Pz-_PG)*(_Pw-_PG))+(_Py*(_PG-_Pw)-_Pv*_PG))/_PA);});}else{return new F(function(){return _PB((_Py+_Pv)/2);});}}}else{return new F(function(){return _PB((_Py+_Pv)/2);});}}else{var _PH=E(_OX),_PI=E(_PH.a),_PJ=_PI.b,_PK=_PI.c,_PL=E(_PH.b),_PM=_PL.b,_PN=_PL.c,_PO=_PK-_PN,_PP=function(_PQ){if(_OS>=_PQ){var _PR=new T(function(){var _PS=B(_OQ(_OR,_OS,_OT,_OU,_Ps));return new T2(0,_PS.a,_PS.b);});return new T2(0,new T3(1,_P0,_PH,new T(function(){return E(E(_PR).a);})),new T(function(){return E(E(_PR).b);}));}else{var _PT=new T(function(){var _PU=B(_OQ(_OR,_OS,_OT,_OU,_P0));return new T2(0,_PU.a,_PU.b);});return new T2(0,new T3(1,new T(function(){return E(E(_PT).a);}),_PH,_Ps),new T(function(){return E(E(_PT).b);}));}};if(_PO!=0){if(_PO<=0){if( -_PO>=1.0e-7){var _PV=E(_OU);return new F(function(){return _PP((_PK*_PM+Math.sqrt(((_PJ-_PM)*(_PJ-_PM)+_PO*_PO)*(_PK-_PV)*(_PN-_PV))+(_PJ*(_PV-_PN)-_PM*_PV))/_PO);});}else{return new F(function(){return _PP((_PJ+_PM)/2);});}}else{if(_PO>=1.0e-7){var _PW=E(_OU);return new F(function(){return _PP((_PK*_PM+Math.sqrt(((_PJ-_PM)*(_PJ-_PM)+_PO*_PO)*(_PK-_PW)*(_PN-_PW))+(_PJ*(_PW-_PN)-_PM*_PW))/_PO);});}else{return new F(function(){return _PP((_PJ+_PM)/2);});}}}else{return new F(function(){return _PP((_PJ+_PM)/2);});}}}}},_PX=function(_PY,_PZ){var _Q0=E(_PZ);if(!_Q0._){return __Z;}else{var _Q1=_Q0.a,_Q2=E(_PY);return (_Q2==1)?new T2(1,_Q1,_6):new T2(1,_Q1,new T(function(){return B(_PX(_Q2-1|0,_Q0.b));}));}},_Q3=__Z,_Q4=function(_Q5){while(1){var _Q6=B((function(_Q7){var _Q8=E(_Q7);if(!_Q8._){return __Z;}else{var _Q9=_Q8.b,_Qa=E(_Q8.a);if(!_Qa._){_Q5=_Q9;return __continue;}else{return new T2(1,_Qa.a,new T(function(){return B(_Q4(_Q9));}));}}})(_Q5));if(_Q6!=__continue){return _Q6;}}},_Qb=function(_Qc,_Qd,_Qe,_Qf){var _Qg=E(_Qd),_Qh=E(_Qe),_Qi=E(_Qf);return new F(function(){return _Lk(_Qc,_Qg.a,_Qg.b,_Qg.c,_Qh.a,_Qh.b,_Qh.c,_Qi.a,_Qi.b,_Qi.c);});},_Qj=function(_Qk,_Ql,_Qm){while(1){var _Qn=E(_Qm);if(!_Qn._){return false;}else{if(!B(A3(_jv,_Qk,_Ql,_Qn.a))){_Qm=_Qn.b;continue;}else{return true;}}}},_Qo=function(_Qp){return new T4(0,1,E(_Qp),E(_IL),E(_IL));},_Qq=function(_Qr,_Qs){var _Qt=E(_Qs);if(!_Qt._){return new F(function(){return _IQ(_Qt.b,B(_Qq(_Qr,_Qt.c)),_Qt.d);});}else{return new F(function(){return _Qo(_Qr);});}},_Qu=function(_Qv,_Qw){var _Qx=E(_Qw);if(!_Qx._){return new F(function(){return _Js(_Qx.b,_Qx.c,B(_Qu(_Qv,_Qx.d)));});}else{return new F(function(){return _Qo(_Qv);});}},_Qy=function(_Qz,_QA,_QB,_QC,_QD){return new F(function(){return _Js(_QB,_QC,B(_Qu(_Qz,_QD)));});},_QE=function(_QF,_QG,_QH,_QI,_QJ){return new F(function(){return _IQ(_QH,B(_Qq(_QF,_QI)),_QJ);});},_QK=function(_QL,_QM,_QN,_QO,_QP,_QQ){var _QR=E(_QM);if(!_QR._){var _QS=_QR.a,_QT=_QR.b,_QU=_QR.c,_QV=_QR.d;if((imul(3,_QS)|0)>=_QN){if((imul(3,_QN)|0)>=_QS){return new T4(0,(_QS+_QN|0)+1|0,E(_QL),E(_QR),E(new T4(0,_QN,E(_QO),E(_QP),E(_QQ))));}else{return new F(function(){return _Js(_QT,_QU,B(_QK(_QL,_QV,_QN,_QO,_QP,_QQ)));});}}else{return new F(function(){return _IQ(_QO,B(_QW(_QL,_QS,_QT,_QU,_QV,_QP)),_QQ);});}}else{return new F(function(){return _QE(_QL,_QN,_QO,_QP,_QQ);});}},_QW=function(_QX,_QY,_QZ,_R0,_R1,_R2){var _R3=E(_R2);if(!_R3._){var _R4=_R3.a,_R5=_R3.b,_R6=_R3.c,_R7=_R3.d;if((imul(3,_QY)|0)>=_R4){if((imul(3,_R4)|0)>=_QY){return new T4(0,(_QY+_R4|0)+1|0,E(_QX),E(new T4(0,_QY,E(_QZ),E(_R0),E(_R1))),E(_R3));}else{return new F(function(){return _Js(_QZ,_R0,B(_QK(_QX,_R1,_R4,_R5,_R6,_R7)));});}}else{return new F(function(){return _IQ(_R5,B(_QW(_QX,_QY,_QZ,_R0,_R1,_R6)),_R7);});}}else{return new F(function(){return _Qy(_QX,_QY,_QZ,_R0,_R1);});}},_R8=function(_R9,_Ra,_Rb){var _Rc=E(_Ra);if(!_Rc._){var _Rd=_Rc.a,_Re=_Rc.b,_Rf=_Rc.c,_Rg=_Rc.d,_Rh=E(_Rb);if(!_Rh._){var _Ri=_Rh.a,_Rj=_Rh.b,_Rk=_Rh.c,_Rl=_Rh.d;if((imul(3,_Rd)|0)>=_Ri){if((imul(3,_Ri)|0)>=_Rd){return new T4(0,(_Rd+_Ri|0)+1|0,E(_R9),E(_Rc),E(_Rh));}else{return new F(function(){return _Js(_Re,_Rf,B(_QK(_R9,_Rg,_Ri,_Rj,_Rk,_Rl)));});}}else{return new F(function(){return _IQ(_Rj,B(_QW(_R9,_Rd,_Re,_Rf,_Rg,_Rk)),_Rl);});}}else{return new F(function(){return _Qy(_R9,_Rd,_Re,_Rf,_Rg);});}}else{return new F(function(){return _Qq(_R9,_Rb);});}},_Rm=function(_Rn,_Ro,_Rp,_Rq){var _Rr=E(_Rq);if(!_Rr._){var _Rs=new T(function(){var _Rt=B(_Rm(_Rr.a,_Rr.b,_Rr.c,_Rr.d));return new T2(0,_Rt.a,_Rt.b);});return new T2(0,new T(function(){return E(E(_Rs).a);}),new T(function(){return B(_IQ(_Ro,_Rp,E(_Rs).b));}));}else{return new T2(0,_Ro,_Rp);}},_Ru=function(_Rv,_Rw,_Rx,_Ry){var _Rz=E(_Rx);if(!_Rz._){var _RA=new T(function(){var _RB=B(_Ru(_Rz.a,_Rz.b,_Rz.c,_Rz.d));return new T2(0,_RB.a,_RB.b);});return new T2(0,new T(function(){return E(E(_RA).a);}),new T(function(){return B(_Js(_Rw,E(_RA).b,_Ry));}));}else{return new T2(0,_Rw,_Ry);}},_RC=function(_RD,_RE){var _RF=E(_RD);if(!_RF._){var _RG=_RF.a,_RH=E(_RE);if(!_RH._){var _RI=_RH.a;if(_RG<=_RI){var _RJ=B(_Ru(_RI,_RH.b,_RH.c,_RH.d));return new F(function(){return _IQ(_RJ.a,_RF,_RJ.b);});}else{var _RK=B(_Rm(_RG,_RF.b,_RF.c,_RF.d));return new F(function(){return _Js(_RK.a,_RK.b,_RH);});}}else{return E(_RF);}}else{return E(_RE);}},_RL=function(_RM,_RN,_RO,_RP,_RQ){var _RR=E(_RM);if(!_RR._){var _RS=_RR.a,_RT=_RR.b,_RU=_RR.c,_RV=_RR.d;if((imul(3,_RS)|0)>=_RN){if((imul(3,_RN)|0)>=_RS){return new F(function(){return _RC(_RR,new T4(0,_RN,E(_RO),E(_RP),E(_RQ)));});}else{return new F(function(){return _Js(_RT,_RU,B(_RL(_RV,_RN,_RO,_RP,_RQ)));});}}else{return new F(function(){return _IQ(_RO,B(_RW(_RS,_RT,_RU,_RV,_RP)),_RQ);});}}else{return new T4(0,_RN,E(_RO),E(_RP),E(_RQ));}},_RW=function(_RX,_RY,_RZ,_S0,_S1){var _S2=E(_S1);if(!_S2._){var _S3=_S2.a,_S4=_S2.b,_S5=_S2.c,_S6=_S2.d;if((imul(3,_RX)|0)>=_S3){if((imul(3,_S3)|0)>=_RX){return new F(function(){return _RC(new T4(0,_RX,E(_RY),E(_RZ),E(_S0)),_S2);});}else{return new F(function(){return _Js(_RY,_RZ,B(_RL(_S0,_S3,_S4,_S5,_S6)));});}}else{return new F(function(){return _IQ(_S4,B(_RW(_RX,_RY,_RZ,_S0,_S5)),_S6);});}}else{return new T4(0,_RX,E(_RY),E(_RZ),E(_S0));}},_S7=function(_S8,_S9){var _Sa=E(_S8);if(!_Sa._){var _Sb=_Sa.a,_Sc=_Sa.b,_Sd=_Sa.c,_Se=_Sa.d,_Sf=E(_S9);if(!_Sf._){var _Sg=_Sf.a,_Sh=_Sf.b,_Si=_Sf.c,_Sj=_Sf.d;if((imul(3,_Sb)|0)>=_Sg){if((imul(3,_Sg)|0)>=_Sb){return new F(function(){return _RC(_Sa,_Sf);});}else{return new F(function(){return _Js(_Sc,_Sd,B(_RL(_Se,_Sg,_Sh,_Si,_Sj)));});}}else{return new F(function(){return _IQ(_Sh,B(_RW(_Sb,_Sc,_Sd,_Se,_Si)),_Sj);});}}else{return E(_Sa);}}else{return E(_S9);}},_Sk=function(_Sl,_Sm){var _Sn=E(_Sm);if(!_Sn._){var _So=_Sn.b,_Sp=_Sn.c,_Sq=_Sn.d;if(!B(A1(_Sl,_So))){return new F(function(){return _S7(B(_Sk(_Sl,_Sp)),B(_Sk(_Sl,_Sq)));});}else{return new F(function(){return _R8(_So,B(_Sk(_Sl,_Sp)),B(_Sk(_Sl,_Sq)));});}}else{return new T0(1);}},_Sr=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_Ss=new T(function(){return B(err(_Sr));}),_St=function(_Su,_Sv,_Sw,_Sx){while(1){var _Sy=E(_Sw);if(!_Sy._){_Su=_Sy.a;_Sv=_Sy.b;_Sw=_Sy.c;_Sx=_Sy.d;continue;}else{return E(_Sv);}}},_Sz=function(_SA,_SB,_SC){return new T3(0,E(_SA),E(_SB),E(_SC));},_SD=function(_SE,_SF){var _SG=E(_SE);if(!_SG._){return __Z;}else{var _SH=E(_SF);return (_SH._==0)?__Z:new T2(1,new T(function(){var _SI=E(_SH.a);return B(_Sz(_SG.a,_SI.a,_SI.b));}),new T(function(){return B(_SD(_SG.b,_SH.b));}));}},_SJ=function(_SK,_SL,_SM,_SN){var _SO=E(_SN);if(!_SO._){var _SP=_SO.c,_SQ=_SO.d,_SR=E(_SO.b),_SS=E(_SK),_ST=E(_SR.a);if(_SS>=_ST){if(_SS!=_ST){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SL,_SM,_SQ)));});}else{var _SU=E(_SL),_SV=E(_SR.b),_SW=E(_SU.a),_SX=E(_SV.a);if(_SW>=_SX){if(_SW!=_SX){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_SM,_SQ)));});}else{var _SY=E(_SU.b),_SZ=E(_SV.b);if(_SY>=_SZ){if(_SY!=_SZ){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_SM,_SQ)));});}else{var _T0=E(_SU.c),_T1=E(_SV.c);if(_T0>=_T1){if(_T0!=_T1){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_SM,_SQ)));});}else{var _T2=E(_SM),_T3=_T2.d,_T4=E(_T2.a),_T5=_T4.a,_T6=_T4.b,_T7=_T4.c,_T8=E(_T2.b),_T9=_T8.a,_Ta=_T8.b,_Tb=_T8.c,_Tc=E(_T2.c),_Td=_Tc.a,_Te=_Tc.b,_Tf=_Tc.c,_Tg=E(_T2.e),_Th=E(_SR.c),_Ti=_Th.d,_Tj=E(_Th.a),_Tk=_Tj.a,_Tl=_Tj.b,_Tm=_Tj.c,_Tn=E(_Th.b),_To=_Tn.a,_Tp=_Tn.b,_Tq=_Tn.c,_Tr=E(_Th.c),_Ts=_Tr.a,_Tt=_Tr.b,_Tu=_Tr.c,_Tv=E(_Th.e);if(_T5>=_Tk){if(_T5!=_Tk){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T6>=_Tl){if(_T6!=_Tl){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T7>=_Tm){if(_T7!=_Tm){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T9>=_To){if(_T9!=_To){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Ta>=_Tp){if(_Ta!=_Tp){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Tb>=_Tq){if(_Tb!=_Tq){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Td>=_Ts){if(_Td!=_Ts){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Te>=_Tt){if(_Te!=_Tt){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Tf>=_Tu){if(_Tf!=_Tu){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T3>=_Ti){if(_T3!=_Ti){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{var _Tw=E(_Tg.a),_Tx=E(_Tv.a);if(_Tw>=_Tx){if(_Tw!=_Tx){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{var _Ty=E(_Tg.b),_Tz=E(_Tv.b);if(_Ty>=_Tz){if(_Ty!=_Tz){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{return new F(function(){return _RC(_SP,_SQ);});}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_SM,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_SM,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_SM,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SL,_SM,_SP)),_SQ);});}}else{return new T0(1);}},_TA=function(_TB,_TC){while(1){var _TD=E(_TC);if(!_TD._){var _TE=E(_TD.b),_TF=B(_SJ(_TE.a,_TE.b,_TE.c,B(_TA(_TB,_TD.d))));_TB=_TF;_TC=_TD.c;continue;}else{return E(_TB);}}},_TG=function(_TH,_TI){while(1){var _TJ=E(_TI);if(!_TJ._){var _TK=E(_TJ.b),_TL=B(_SJ(_TK.a,_TK.b,_TK.c,B(_TG(_TH,_TJ.d))));_TH=_TL;_TI=_TJ.c;continue;}else{return E(_TH);}}},_TM=function(_TN,_TO,_TP){while(1){var _TQ=E(_TP);if(!_TQ._){return E(_TO);}else{_TN=_TQ.a;_TO=_TQ.b;_TP=_TQ.c;continue;}}},_TR=new T(function(){return B(unCStr("lookFor: Breakpoint does not exist."));}),_TS=new T(function(){return B(err(_TR));}),_TT=function(_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U1){var _U2=E(_U1);if(!_U2._){return __Z;}else{var _U3=E(_U2.b),_U4=E(_U3.a),_U5=_U4.b,_U6=_U4.c,_U7=E(_U3.b),_U8=_U7.b,_U9=_U7.c,_Ua=function(_Ub){var _Uc=_TW-_TZ,_Ud=function(_Ue){var _Uf=_U6-_U9,_Ug=function(_Uh){if(_Ue>=_Uh){if(_Ue<_Uh){return E(_TS);}else{return new F(function(){return _TT(_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U2.c);});}}else{return new F(function(){return _TT(_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U2.a);});}};if(_Uf!=0){if(_Uf<=0){if( -_Uf>=1.0e-7){var _Ui=E(_U0);return new F(function(){return _Ug((_U6*_U8+Math.sqrt(((_U5-_U8)*(_U5-_U8)+_Uf*_Uf)*(_U6-_Ui)*(_U9-_Ui))+(_U5*(_Ui-_U9)-_U8*_Ui))/_Uf);});}else{return new F(function(){return _Ug((_U5+_U8)/2);});}}else{if(_Uf>=1.0e-7){var _Uj=E(_U0);return new F(function(){return _Ug((_U6*_U8+Math.sqrt(((_U5-_U8)*(_U5-_U8)+_Uf*_Uf)*(_U6-_Uj)*(_U9-_Uj))+(_U5*(_Uj-_U9)-_U8*_Uj))/_Uf);});}else{return new F(function(){return _Ug((_U5+_U8)/2);});}}}else{return new F(function(){return _Ug((_U5+_U8)/2);});}};if(_Uc!=0){if(_Uc<=0){if( -_Uc>=1.0e-7){var _Uk=E(_U0);return new F(function(){return _Ud((_TW*_TY+Math.sqrt(((_TV-_TY)*(_TV-_TY)+_Uc*_Uc)*(_TW-_Uk)*(_TZ-_Uk))+(_TV*(_Uk-_TZ)-_TY*_Uk))/_Uc);});}else{return new F(function(){return _Ud((_TV+_TY)/2);});}}else{if(_Uc>=1.0e-7){var _Ul=E(_U0);return new F(function(){return _Ud((_TW*_TY+Math.sqrt(((_TV-_TY)*(_TV-_TY)+_Uc*_Uc)*(_TW-_Ul)*(_TZ-_Ul))+(_TV*(_Ul-_TZ)-_TY*_Ul))/_Uc);});}else{return new F(function(){return _Ud((_TV+_TY)/2);});}}}else{return new F(function(){return _Ud((_TV+_TY)/2);});}};if(_U4.a!=_TU){return new F(function(){return _Ua(_);});}else{if(_U7.a!=_TX){return new F(function(){return _Ua(_);});}else{return E(_U2);}}}},_Um=function(_Un,_Uo,_Up){var _Uq=E(_Up);if(!_Uq._){return __Z;}else{var _Ur=E(_Uq.b),_Us=E(_Ur.a),_Ut=_Us.b,_Uu=_Us.c,_Uv=E(_Ur.b),_Uw=_Uv.b,_Ux=_Uv.c,_Uy=E(_Un),_Uz=E(_Uy.a),_UA=_Uz.a,_UB=_Uz.b,_UC=_Uz.c,_UD=E(_Uy.b),_UE=_UD.a,_UF=_UD.b,_UG=_UD.c,_UH=function(_UI){var _UJ=_UC-_UG,_UK=function(_UL){var _UM=_Uu-_Ux,_UN=function(_UO){if(_UL>=_UO){if(_UL<_UO){return E(_TS);}else{return new F(function(){return _TT(_UA,_UB,_UC,_UE,_UF,_UG,_Uo,_Uq.c);});}}else{return new F(function(){return _TT(_UA,_UB,_UC,_UE,_UF,_UG,_Uo,_Uq.a);});}};if(_UM!=0){if(_UM<=0){if( -_UM>=1.0e-7){var _UP=E(_Uo);return new F(function(){return _UN((_Uu*_Uw+Math.sqrt(((_Ut-_Uw)*(_Ut-_Uw)+_UM*_UM)*(_Uu-_UP)*(_Ux-_UP))+(_Ut*(_UP-_Ux)-_Uw*_UP))/_UM);});}else{return new F(function(){return _UN((_Ut+_Uw)/2);});}}else{if(_UM>=1.0e-7){var _UQ=E(_Uo);return new F(function(){return _UN((_Uu*_Uw+Math.sqrt(((_Ut-_Uw)*(_Ut-_Uw)+_UM*_UM)*(_Uu-_UQ)*(_Ux-_UQ))+(_Ut*(_UQ-_Ux)-_Uw*_UQ))/_UM);});}else{return new F(function(){return _UN((_Ut+_Uw)/2);});}}}else{return new F(function(){return _UN((_Ut+_Uw)/2);});}};if(_UJ!=0){if(_UJ<=0){if( -_UJ>=1.0e-7){var _UR=E(_Uo);return new F(function(){return _UK((_UC*_UF+Math.sqrt(((_UB-_UF)*(_UB-_UF)+_UJ*_UJ)*(_UC-_UR)*(_UG-_UR))+(_UB*(_UR-_UG)-_UF*_UR))/_UJ);});}else{return new F(function(){return _UK((_UB+_UF)/2);});}}else{if(_UJ>=1.0e-7){var _US=E(_Uo);return new F(function(){return _UK((_UC*_UF+Math.sqrt(((_UB-_UF)*(_UB-_UF)+_UJ*_UJ)*(_UC-_US)*(_UG-_US))+(_UB*(_US-_UG)-_UF*_US))/_UJ);});}else{return new F(function(){return _UK((_UB+_UF)/2);});}}}else{return new F(function(){return _UK((_UB+_UF)/2);});}};if(_Us.a!=_UA){return new F(function(){return _UH(_);});}else{if(_Uv.a!=_UE){return new F(function(){return _UH(_);});}else{return E(_Uq);}}}},_UT=new T3(0,0,0,0),_UU=new T2(0,E(_UT),E(_UT)),_UV=function(_UW,_UX,_UY){var _UZ=function(_V0){var _V1=E(_UY);if(!_V1._){return E(_UU);}else{var _V2=E(_V1.b),_V3=E(_V2.a),_V4=_V3.b,_V5=_V3.c,_V6=E(_V2.b),_V7=_V6.b,_V8=_V6.c,_V9=E(_UW),_Va=E(_V9.a),_Vb=_Va.a,_Vc=E(_V9.b),_Vd=_Vc.a,_Ve=function(_Vf){var _Vg=B(_NC(_Va.b,_Va.c,_Vc.b,_Vc.c,_UX)),_Vh=_V5-_V8,_Vi=function(_Vj){if(_Vg>=_Vj){if(_Vg<=_Vj){return E(_UU);}else{var _Vk=function(_Vl,_Vm){var _Vn=E(_Vm);if(!_Vn._){return E(_Vl);}else{var _Vo=E(_Vn.b),_Vp=E(_Vo.a),_Vq=_Vp.b,_Vr=_Vp.c,_Vs=E(_Vo.b),_Vt=_Vs.b,_Vu=_Vs.c,_Vv=function(_Vw){var _Vx=_Vr-_Vu,_Vy=function(_Vz){if(_Vg>=_Vz){if(_Vg<=_Vz){return E(_Vl);}else{return new F(function(){return _Vk(_Vo,_Vn.c);});}}else{return new F(function(){return _Vk(_Vl,_Vn.a);});}};if(_Vx!=0){if(_Vx<=0){if( -_Vx>=1.0e-7){var _VA=E(_UX);return new F(function(){return _Vy((_Vr*_Vt+Math.sqrt(((_Vq-_Vt)*(_Vq-_Vt)+_Vx*_Vx)*(_Vr-_VA)*(_Vu-_VA))+(_Vq*(_VA-_Vu)-_Vt*_VA))/_Vx);});}else{return new F(function(){return _Vy((_Vq+_Vt)/2);});}}else{if(_Vx>=1.0e-7){var _VB=E(_UX);return new F(function(){return _Vy((_Vr*_Vt+Math.sqrt(((_Vq-_Vt)*(_Vq-_Vt)+_Vx*_Vx)*(_Vr-_VB)*(_Vu-_VB))+(_Vq*(_VB-_Vu)-_Vt*_VB))/_Vx);});}else{return new F(function(){return _Vy((_Vq+_Vt)/2);});}}}else{return new F(function(){return _Vy((_Vq+_Vt)/2);});}};if(_Vp.a!=_Vb){return new F(function(){return _Vv(_);});}else{if(_Vs.a!=_Vd){return new F(function(){return _Vv(_);});}else{return E(_Vl);}}}};return new F(function(){return _Vk(_V2,_V1.c);});}}else{var _VC=function(_VD,_VE){var _VF=E(_VE);if(!_VF._){return E(_VD);}else{var _VG=E(_VF.b),_VH=E(_VG.a),_VI=_VH.b,_VJ=_VH.c,_VK=E(_VG.b),_VL=_VK.b,_VM=_VK.c,_VN=function(_VO){var _VP=_VJ-_VM,_VQ=function(_VR){if(_Vg>=_VR){if(_Vg<=_VR){return E(_VD);}else{return new F(function(){return _VC(_VG,_VF.c);});}}else{return new F(function(){return _VC(_VD,_VF.a);});}};if(_VP!=0){if(_VP<=0){if( -_VP>=1.0e-7){var _VS=E(_UX);return new F(function(){return _VQ((_VJ*_VL+Math.sqrt(((_VI-_VL)*(_VI-_VL)+_VP*_VP)*(_VJ-_VS)*(_VM-_VS))+(_VI*(_VS-_VM)-_VL*_VS))/_VP);});}else{return new F(function(){return _VQ((_VI+_VL)/2);});}}else{if(_VP>=1.0e-7){var _VT=E(_UX);return new F(function(){return _VQ((_VJ*_VL+Math.sqrt(((_VI-_VL)*(_VI-_VL)+_VP*_VP)*(_VJ-_VT)*(_VM-_VT))+(_VI*(_VT-_VM)-_VL*_VT))/_VP);});}else{return new F(function(){return _VQ((_VI+_VL)/2);});}}}else{return new F(function(){return _VQ((_VI+_VL)/2);});}};if(_VH.a!=_Vb){return new F(function(){return _VN(_);});}else{if(_VK.a!=_Vd){return new F(function(){return _VN(_);});}else{return E(_VD);}}}};return new F(function(){return _VC(_UU,_V1.a);});}};if(_Vh!=0){if(_Vh<=0){if( -_Vh>=1.0e-7){var _VU=E(_UX);return new F(function(){return _Vi((_V5*_V7+Math.sqrt(((_V4-_V7)*(_V4-_V7)+_Vh*_Vh)*(_V5-_VU)*(_V8-_VU))+(_V4*(_VU-_V8)-_V7*_VU))/_Vh);});}else{return new F(function(){return _Vi((_V4+_V7)/2);});}}else{if(_Vh>=1.0e-7){var _VV=E(_UX);return new F(function(){return _Vi((_V5*_V7+Math.sqrt(((_V4-_V7)*(_V4-_V7)+_Vh*_Vh)*(_V5-_VV)*(_V8-_VV))+(_V4*(_VV-_V8)-_V7*_VV))/_Vh);});}else{return new F(function(){return _Vi((_V4+_V7)/2);});}}}else{return new F(function(){return _Vi((_V4+_V7)/2);});}};if(_V3.a!=_Vb){return new F(function(){return _Ve(_);});}else{if(_V6.a!=_Vd){return new F(function(){return _Ve(_);});}else{return E(_UU);}}}},_VW=B(_Um(_UW,_UX,_UY));if(!_VW._){return new F(function(){return _UZ(_);});}else{var _VX=E(_VW.a);if(!_VX._){return new F(function(){return _UZ(_);});}else{return new F(function(){return _TM(_VX.a,_VX.b,_VX.c);});}}},_VY=function(_VZ,_W0,_W1){var _W2=function(_W3){var _W4=E(_W1);if(!_W4._){return E(_UU);}else{var _W5=E(_W4.b),_W6=E(_W5.a),_W7=_W6.b,_W8=_W6.c,_W9=E(_W5.b),_Wa=_W9.b,_Wb=_W9.c,_Wc=E(_VZ),_Wd=E(_Wc.a),_We=_Wd.a,_Wf=E(_Wc.b),_Wg=_Wf.a,_Wh=function(_Wi){var _Wj=B(_NC(_Wd.b,_Wd.c,_Wf.b,_Wf.c,_W0)),_Wk=_W8-_Wb,_Wl=function(_Wm){if(_Wj>=_Wm){if(_Wj<=_Wm){return E(_UU);}else{var _Wn=function(_Wo,_Wp){var _Wq=E(_Wp);if(!_Wq._){return E(_Wo);}else{var _Wr=E(_Wq.b),_Ws=E(_Wr.a),_Wt=_Ws.b,_Wu=_Ws.c,_Wv=E(_Wr.b),_Ww=_Wv.b,_Wx=_Wv.c,_Wy=function(_Wz){var _WA=_Wu-_Wx,_WB=function(_WC){if(_Wj>=_WC){if(_Wj<=_WC){return E(_Wo);}else{return new F(function(){return _Wn(_Wo,_Wq.c);});}}else{return new F(function(){return _Wn(_Wr,_Wq.a);});}};if(_WA!=0){if(_WA<=0){if( -_WA>=1.0e-7){var _WD=E(_W0);return new F(function(){return _WB((_Wu*_Ww+Math.sqrt(((_Wt-_Ww)*(_Wt-_Ww)+_WA*_WA)*(_Wu-_WD)*(_Wx-_WD))+(_Wt*(_WD-_Wx)-_Ww*_WD))/_WA);});}else{return new F(function(){return _WB((_Wt+_Ww)/2);});}}else{if(_WA>=1.0e-7){var _WE=E(_W0);return new F(function(){return _WB((_Wu*_Ww+Math.sqrt(((_Wt-_Ww)*(_Wt-_Ww)+_WA*_WA)*(_Wu-_WE)*(_Wx-_WE))+(_Wt*(_WE-_Wx)-_Ww*_WE))/_WA);});}else{return new F(function(){return _WB((_Wt+_Ww)/2);});}}}else{return new F(function(){return _WB((_Wt+_Ww)/2);});}};if(_Ws.a!=_We){return new F(function(){return _Wy(_);});}else{if(_Wv.a!=_Wg){return new F(function(){return _Wy(_);});}else{return E(_Wo);}}}};return new F(function(){return _Wn(_UU,_W4.c);});}}else{var _WF=function(_WG,_WH){var _WI=E(_WH);if(!_WI._){return E(_WG);}else{var _WJ=E(_WI.b),_WK=E(_WJ.a),_WL=_WK.b,_WM=_WK.c,_WN=E(_WJ.b),_WO=_WN.b,_WP=_WN.c,_WQ=function(_WR){var _WS=_WM-_WP,_WT=function(_WU){if(_Wj>=_WU){if(_Wj<=_WU){return E(_WG);}else{return new F(function(){return _WF(_WG,_WI.c);});}}else{return new F(function(){return _WF(_WJ,_WI.a);});}};if(_WS!=0){if(_WS<=0){if( -_WS>=1.0e-7){var _WV=E(_W0);return new F(function(){return _WT((_WM*_WO+Math.sqrt(((_WL-_WO)*(_WL-_WO)+_WS*_WS)*(_WM-_WV)*(_WP-_WV))+(_WL*(_WV-_WP)-_WO*_WV))/_WS);});}else{return new F(function(){return _WT((_WL+_WO)/2);});}}else{if(_WS>=1.0e-7){var _WW=E(_W0);return new F(function(){return _WT((_WM*_WO+Math.sqrt(((_WL-_WO)*(_WL-_WO)+_WS*_WS)*(_WM-_WW)*(_WP-_WW))+(_WL*(_WW-_WP)-_WO*_WW))/_WS);});}else{return new F(function(){return _WT((_WL+_WO)/2);});}}}else{return new F(function(){return _WT((_WL+_WO)/2);});}};if(_WK.a!=_We){return new F(function(){return _WQ(_);});}else{if(_WN.a!=_Wg){return new F(function(){return _WQ(_);});}else{return E(_WG);}}}};return new F(function(){return _WF(_W5,_W4.a);});}};if(_Wk!=0){if(_Wk<=0){if( -_Wk>=1.0e-7){var _WX=E(_W0);return new F(function(){return _Wl((_W8*_Wa+Math.sqrt(((_W7-_Wa)*(_W7-_Wa)+_Wk*_Wk)*(_W8-_WX)*(_Wb-_WX))+(_W7*(_WX-_Wb)-_Wa*_WX))/_Wk);});}else{return new F(function(){return _Wl((_W7+_Wa)/2);});}}else{if(_Wk>=1.0e-7){var _WY=E(_W0);return new F(function(){return _Wl((_W8*_Wa+Math.sqrt(((_W7-_Wa)*(_W7-_Wa)+_Wk*_Wk)*(_W8-_WY)*(_Wb-_WY))+(_W7*(_WY-_Wb)-_Wa*_WY))/_Wk);});}else{return new F(function(){return _Wl((_W7+_Wa)/2);});}}}else{return new F(function(){return _Wl((_W7+_Wa)/2);});}};if(_W6.a!=_We){return new F(function(){return _Wh(_);});}else{if(_W9.a!=_Wg){return new F(function(){return _Wh(_);});}else{return E(_UU);}}}},_WZ=B(_Um(_VZ,_W0,_W1));if(!_WZ._){return new F(function(){return _W2(_);});}else{var _X0=E(_WZ.c);if(!_X0._){return new F(function(){return _W2(_);});}else{return new F(function(){return _LG(_X0.a,_X0.b,_X0.c);});}}},_X1=function(_X2,_X3,_X4,_X5){var _X6=E(_X5);if(!_X6._){return new T3(1,_ON,_X3,_ON);}else{var _X7=_X6.a,_X8=_X6.c,_X9=E(_X6.b),_Xa=E(_X9.a),_Xb=_Xa.b,_Xc=_Xa.c,_Xd=E(_X9.b),_Xe=_Xd.b,_Xf=_Xd.c,_Xg=_Xc-_Xf,_Xh=function(_Xi){return (_X2>=_Xi)?new T3(1,_X7,_X9,new T(function(){return B(_X1(_X2,_X3,_X4,_X8));})):new T3(1,new T(function(){return B(_X1(_X2,_X3,_X4,_X7));}),_X9,_X8);};if(_Xg!=0){if(_Xg<=0){if( -_Xg>=1.0e-7){var _Xj=E(_X4);return new F(function(){return _Xh((_Xc*_Xe+Math.sqrt(((_Xb-_Xe)*(_Xb-_Xe)+_Xg*_Xg)*(_Xc-_Xj)*(_Xf-_Xj))+(_Xb*(_Xj-_Xf)-_Xe*_Xj))/_Xg);});}else{return new F(function(){return _Xh((_Xb+_Xe)/2);});}}else{if(_Xg>=1.0e-7){var _Xk=E(_X4);return new F(function(){return _Xh((_Xc*_Xe+Math.sqrt(((_Xb-_Xe)*(_Xb-_Xe)+_Xg*_Xg)*(_Xc-_Xk)*(_Xf-_Xk))+(_Xb*(_Xk-_Xf)-_Xe*_Xk))/_Xg);});}else{return new F(function(){return _Xh((_Xb+_Xe)/2);});}}}else{return new F(function(){return _Xh((_Xb+_Xe)/2);});}}},_Xl=function(_Xm,_Xn,_Xo,_Xp){var _Xq=E(_Xp);if(!_Xq._){return new T3(1,_ON,_Xn,_ON);}else{var _Xr=_Xq.a,_Xs=_Xq.c,_Xt=E(_Xm),_Xu=E(_Xq.b),_Xv=E(_Xu.a),_Xw=_Xv.b,_Xx=_Xv.c,_Xy=E(_Xu.b),_Xz=_Xy.b,_XA=_Xy.c,_XB=_Xx-_XA,_XC=function(_XD){return (_Xt>=_XD)?new T3(1,_Xr,_Xu,new T(function(){return B(_X1(_Xt,_Xn,_Xo,_Xs));})):new T3(1,new T(function(){return B(_X1(_Xt,_Xn,_Xo,_Xr));}),_Xu,_Xs);};if(_XB!=0){if(_XB<=0){if( -_XB>=1.0e-7){var _XE=E(_Xo);return new F(function(){return _XC((_Xx*_Xz+Math.sqrt(((_Xw-_Xz)*(_Xw-_Xz)+_XB*_XB)*(_Xx-_XE)*(_XA-_XE))+(_Xw*(_XE-_XA)-_Xz*_XE))/_XB);});}else{return new F(function(){return _XC((_Xw+_Xz)/2);});}}else{if(_XB>=1.0e-7){var _XF=E(_Xo);return new F(function(){return _XC((_Xx*_Xz+Math.sqrt(((_Xw-_Xz)*(_Xw-_Xz)+_XB*_XB)*(_Xx-_XF)*(_XA-_XF))+(_Xw*(_XF-_XA)-_Xz*_XF))/_XB);});}else{return new F(function(){return _XC((_Xw+_Xz)/2);});}}}else{return new F(function(){return _XC((_Xw+_Xz)/2);});}}},_XG=0,_XH=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_XI=function(_XJ){return new F(function(){return _7B(new T1(0,new T(function(){return B(_7O(_XJ,_XH));})),_7l);});},_XK=new T(function(){return B(_XI("Fortune/Fortune.hs:(311,19)-(314,56)|multi-way if"));}),_XL=function(_XM,_XN){var _XO=E(_XM);return new F(function(){return _K2(_Iy,new T3(0,_XO.d,new T3(0,E(_XO.a).a,E(_XO.b).a,E(_XO.c).a),_XO),_XN);});},_XP=new T(function(){return B(_7Z("Fortune/Fortune.hs:(117,1)-(118,32)|function setVert"));}),_XQ=function(_XR,_XS){var _XT=E(E(_XR).a),_XU=E(E(_XS).a);return (_XT>=_XU)?(_XT!=_XU)?2:1:0;},_XV=function(_XW){var _XX=E(_XW),_XY=E(_XX.b);return new T2(0,_XY,_XX);},_XZ=0,_Y0=new T3(0,_XZ,_XZ,_XZ),_Y1=function(_Y2,_Y3){if(_Y2<=_Y3){var _Y4=function(_Y5){return new T2(1,_Y5,new T(function(){if(_Y5!=_Y3){return B(_Y4(_Y5+1|0));}else{return __Z;}}));};return new F(function(){return _Y4(_Y2);});}else{return __Z;}},_Y6=new T(function(){return B(_Y1(0,2147483647));}),_Y7=function(_Y8,_Y9){var _Ya=E(_Y9);return (_Ya._==0)?__Z:new T2(1,new T(function(){return B(A1(_Y8,_Ya.a));}),new T(function(){return B(_Y7(_Y8,_Ya.b));}));},_Yb=new T(function(){return B(unCStr("tail"));}),_Yc=new T(function(){return B(_eZ(_Yb));}),_Yd=function(_Ye){return E(E(_Ye).b);},_Yf=new T2(1,_6,_6),_Yg=function(_Yh,_Yi){var _Yj=function(_Yk,_Yl){var _Ym=E(_Yk);if(!_Ym._){return E(_Yl);}else{var _Yn=_Ym.a,_Yo=E(_Yl);if(!_Yo._){return E(_Ym);}else{var _Yp=_Yo.a;return (B(A2(_Yh,_Yn,_Yp))==2)?new T2(1,_Yp,new T(function(){return B(_Yj(_Ym,_Yo.b));})):new T2(1,_Yn,new T(function(){return B(_Yj(_Ym.b,_Yo));}));}}},_Yq=function(_Yr){var _Ys=E(_Yr);if(!_Ys._){return __Z;}else{var _Yt=E(_Ys.b);return (_Yt._==0)?E(_Ys):new T2(1,new T(function(){return B(_Yj(_Ys.a,_Yt.a));}),new T(function(){return B(_Yq(_Yt.b));}));}},_Yu=new T(function(){return B(_Yv(B(_Yq(_6))));}),_Yv=function(_Yw){while(1){var _Yx=E(_Yw);if(!_Yx._){return E(_Yu);}else{if(!E(_Yx.b)._){return E(_Yx.a);}else{_Yw=B(_Yq(_Yx));continue;}}}},_Yy=new T(function(){return B(_Yz(_6));}),_YA=function(_YB,_YC,_YD){while(1){var _YE=B((function(_YF,_YG,_YH){var _YI=E(_YH);if(!_YI._){return new T2(1,new T2(1,_YF,_YG),_Yy);}else{var _YJ=_YI.a;if(B(A2(_Yh,_YF,_YJ))==2){var _YK=new T2(1,_YF,_YG);_YB=_YJ;_YC=_YK;_YD=_YI.b;return __continue;}else{return new T2(1,new T2(1,_YF,_YG),new T(function(){return B(_Yz(_YI));}));}}})(_YB,_YC,_YD));if(_YE!=__continue){return _YE;}}},_YL=function(_YM,_YN,_YO){while(1){var _YP=B((function(_YQ,_YR,_YS){var _YT=E(_YS);if(!_YT._){return new T2(1,new T(function(){return B(A1(_YR,new T2(1,_YQ,_6)));}),_Yy);}else{var _YU=_YT.a,_YV=_YT.b;switch(B(A2(_Yh,_YQ,_YU))){case 0:_YM=_YU;_YN=function(_YW){return new F(function(){return A1(_YR,new T2(1,_YQ,_YW));});};_YO=_YV;return __continue;case 1:_YM=_YU;_YN=function(_YX){return new F(function(){return A1(_YR,new T2(1,_YQ,_YX));});};_YO=_YV;return __continue;default:return new T2(1,new T(function(){return B(A1(_YR,new T2(1,_YQ,_6)));}),new T(function(){return B(_Yz(_YT));}));}}})(_YM,_YN,_YO));if(_YP!=__continue){return _YP;}}},_Yz=function(_YY){var _YZ=E(_YY);if(!_YZ._){return E(_Yf);}else{var _Z0=_YZ.a,_Z1=E(_YZ.b);if(!_Z1._){return new T2(1,_YZ,_6);}else{var _Z2=_Z1.a,_Z3=_Z1.b;if(B(A2(_Yh,_Z0,_Z2))==2){return new F(function(){return _YA(_Z2,new T2(1,_Z0,_6),_Z3);});}else{return new F(function(){return _YL(_Z2,function(_Z4){return new T2(1,_Z0,_Z4);},_Z3);});}}}};return new F(function(){return _Yv(B(_Yz(_Yi)));});},_Z5=function(_Z6,_Z7,_Z8){var _Z9=function(_Za,_Zb){while(1){var _Zc=B((function(_Zd,_Ze){var _Zf=E(_Ze);if(!_Zf._){var _Zg=_Zf.e,_Zh=E(_Zf.b),_Zi=_Zh.a,_Zj=_Zh.b,_Zk=new T(function(){var _Zl=E(_Zf.c);switch(_Zl._){case 0:return B(_Z9(_Zd,_Zg));break;case 1:var _Zm=E(_Zl.a),_Zn=E(_Zm.a);if(_Zn<0){return B(_Z9(_Zd,_Zg));}else{var _Zo=E(_Z7);if(_Zn>_Zo){return B(_Z9(_Zd,_Zg));}else{var _Zp=E(_Zm.b);if(_Zp<0){return B(_Z9(_Zd,_Zg));}else{var _Zq=E(_Z8);if(_Zp>_Zq){return B(_Z9(_Zd,_Zg));}else{var _Zr=B(_oU(_Z6,E(_Zi))),_Zs=E(_Zr.a),_Zt=E(_Zr.b),_Zu=B(_oU(_Z6,E(_Zj))),_Zv=E(_Zu.a),_Zw=E(_Zu.b),_Zx=Math.pow(_Zn-_Zs,2)+Math.pow(_Zp-_Zt,2)-(Math.pow(_Zn-_Zv,2)+Math.pow(_Zp-_Zw,2)),_Zy=function(_Zz,_ZA){var _ZB=E(_ZA);if(_ZB._==2){return new T2(1,new T(function(){var _ZC=E(_Zz);return new T4(0,E(_ZC.a),E(_ZC.b),E(_ZB.a),E(_ZB.b));}),new T(function(){return B(_Z9(_Zd,_Zg));}));}else{return new F(function(){return _Z9(_Zd,_Zg);});}},_ZD=function(_ZE){if(_ZE>=1.0e-2){return new T2(0,_Zh,_Zl);}else{var _ZF=new T(function(){var _ZG=_Zv-_Zs,_ZH=(Math.pow(_Zv,2)-Math.pow(_Zs,2)+Math.pow(_Zw,2)-Math.pow(_Zt,2))/2,_ZI=_Zw-_Zt,_ZJ=function(_ZK,_ZL){var _ZM=B(_PX(2,B(_Yg(function(_ZN,_ZO){var _ZP=E(_ZN),_ZQ=E(_ZL),_ZR=E(_ZO),_ZS=Math.pow(_ZK-E(_ZP.a),2)+Math.pow(_ZQ-E(_ZP.b),2),_ZT=Math.pow(_ZK-E(_ZR.a),2)+Math.pow(_ZQ-E(_ZR.b),2);return (_ZS>=_ZT)?(_ZS!=_ZT)?2:1:0;},_Z6))));if(!B(_Qj(_AW,_Zr,_ZM))){return false;}else{return new F(function(){return _Qj(_AW,_Zu,_ZM);});}},_ZU=function(_ZV,_ZW){var _ZX=B(_PX(2,B(_Yg(function(_ZY,_ZZ){var _100=E(_ZY),_101=E(_ZV),_102=E(_ZZ),_103=Math.pow(_101-E(_100.a),2)+Math.pow(_ZW-E(_100.b),2),_104=Math.pow(_101-E(_102.a),2)+Math.pow(_ZW-E(_102.b),2);return (_103>=_104)?(_103!=_104)?2:1:0;},_Z6))));if(!B(_Qj(_AW,_Zr,_ZX))){return false;}else{return new F(function(){return _Qj(_AW,_Zu,_ZX);});}},_105=function(_106){if(_Zw!=_Zt){var _107=new T(function(){return (_ZH-_ZG*0)/_ZI;}),_108=new T(function(){var _109=new T(function(){return (_ZH-_ZG*_Zo)/_ZI;});if(!B(_ZJ(0,_109))){return __Z;}else{return new T2(1,new T2(0,_XG,_109),_6);}});return (!B(_ZJ(0,_107)))?E(_108):new T2(1,new T2(0,_XG,_107),_108);}else{if(_Zv!=_Zs){var _10a=new T(function(){return (_ZH-_ZI*0)/_ZG;}),_10b=new T(function(){var _10c=new T(function(){return (_ZH-_ZI*_Zq)/_ZG;});if(!B(_ZU(_10c,_Zq))){return __Z;}else{return new T2(1,new T2(0,_10c,_Zq),_6);}});return (!B(_ZU(_10a,0)))?E(_10b):new T2(1,new T2(0,_10a,_XG),_10b);}else{return E(_XK);}}},_10d=function(_10e,_10f){var _10g=E(_10e),_10h=E(_10f),_10i=Math.pow(_Zn-E(_10g.a),2)+Math.pow(_Zp-E(_10g.b),2),_10j=Math.pow(_Zn-E(_10h.a),2)+Math.pow(_Zp-E(_10h.b),2);return (_10i>=_10j)?(_10i!=_10j)?E(_10h):E(_10g):E(_10g);};if(_Zw!=_Zt){if(_Zv!=_Zs){var _10k=new T(function(){return (_ZH-_ZG*0)/_ZI;}),_10l=new T(function(){var _10m=new T(function(){return (_ZH-_ZG*_Zo)/_ZI;}),_10n=new T(function(){var _10o=new T(function(){return (_ZH-_ZI*0)/_ZG;}),_10p=new T(function(){var _10q=new T(function(){return (_ZH-_ZI*_Zq)/_ZG;});if(!B(_ZU(_10q,_Zq))){return __Z;}else{return new T2(1,new T2(0,_10q,_Zq),_6);}});if(!B(_ZU(_10o,0))){return E(_10p);}else{return new T2(1,new T2(0,_10o,_XG),_10p);}});if(!B(_ZJ(0,_10m))){return E(_10n);}else{return new T2(1,new T2(0,_XG,_10m),_10n);}});if(!B(_ZJ(0,_10k))){var _10r=B(_f3(_10d,_10l));}else{var _10r=B(_f3(_10d,new T2(1,new T2(0,_XG,_10k),_10l)));}var _10s=_10r;}else{var _10s=B(_f3(_10d,B(_105(_))));}var _10t=_10s;}else{var _10t=B(_f3(_10d,B(_105(_))));}return new T2(2,E(_Zm),E(_10t));});return new T2(0,_Zh,_ZF);}};if(_Zx!=0){if(_Zx<=0){var _10u=B(_ZD( -_Zx));return B(_Zy(_10u.a,_10u.b));}else{var _10v=B(_ZD(_Zx));return B(_Zy(_10v.a,_10v.b));}}else{var _10w=B(_ZD(0));return B(_Zy(_10w.a,_10w.b));}}}}}break;default:return new T2(1,new T(function(){return new T4(0,E(_Zi),E(_Zj),E(_Zl.a),E(_Zl.b));}),new T(function(){return B(_Z9(_Zd,_Zg));}));}},1);_Za=_Zk;_Zb=_Zf.d;return __continue;}else{return E(_Zd);}})(_Za,_Zb));if(_Zc!=__continue){return _Zc;}}},_10x=function(_10y,_10z,_10A){var _10B=new T(function(){var _10C=E(_10y),_10D=_10C.b,_10E=_10C.c,_10F=_10C.d,_10G=E(_10C.a),_10H=_10G.a,_10I=_10G.b,_10J=new T(function(){var _10K=new T(function(){var _10L=function(_10M){var _10N=new T(function(){var _10O=E(_10I);if(!_10O._){var _10P=E(_10O.c);if(!_10P._){return B(_St(_10P.a,_10P.b,_10P.c,_10P.d));}else{return E(_10O.b);}}else{return E(_Ss);}}),_10Q=function(_10R){var _10S=new T(function(){var _10T=E(_10F);return new T5(0,1,E(_10T),new T4(0,_ch,_10E,_10D,new T(function(){return E(E(_10N).b);})),E(_wq),E(_wq));}),_10U=new T(function(){var _10V=E(_10I);if(!_10V._){var _10W=E(_10V.c);if(!_10W._){var _10X=E(B(_St(_10W.a,_10W.b,_10W.c,_10W.d)).c),_10Y=E(_10X.a),_10Z=E(_10X.b),_110=E(_10X.c);return {_:0,a:_10Y,b:_10Y.a,c:_10Z,d:_10Z.a,e:_110,f:_110.a,g:_10X.d,h:_10X.e};}else{var _111=E(E(_10V.b).c),_112=E(_111.a),_113=E(_111.b),_114=E(_111.c);return {_:0,a:_112,b:_112.a,c:_113,d:_113.a,e:_114,f:_114.a,g:_111.d,h:_111.e};}}else{return E(_Ss);}}),_115=new T(function(){return E(E(_10U).h);}),_116=new T(function(){return E(E(_10U).a);}),_117=new T(function(){return E(E(_10U).c);}),_118=new T(function(){return new T2(0,E(_116),E(_117));}),_119=new T(function(){return E(E(_10U).g);}),_11a=new T(function(){return (E(_119)+E(_10F))/2;}),_11b=new T(function(){return E(E(_10U).e);}),_11c=new T(function(){return new T2(0,E(_117),E(_11b));}),_11d=new T(function(){var _11e=E(_116).a,_11f=E(_11b).a,_11g=E(_117).a,_11h=function(_11i,_11j){var _11k=function(_11l,_11m){var _11n=new T(function(){return new T1(1,E(_115));}),_11o=function(_11p,_11q){return new T1(1,new T(function(){var _11r=E(_11q);switch(_11r._){case 0:return E(_11n);break;case 1:return new T2(2,E(_11r.a),E(_115));break;default:return E(_XP);}}));},_11s=function(_11t,_11u){return new T1(1,new T(function(){var _11v=E(_11u);switch(_11v._){case 0:return E(_11n);break;case 1:return new T2(2,E(_11v.a),E(_115));break;default:return E(_XP);}}));},_11w=B(_L5(_11s,_11i,_11j,B(_L5(_11o,_11l,_11m,_10E))));if(_11e>=_11f){return new F(function(){return _Iz(_11f,_11e,_11n,_11w);});}else{return new F(function(){return _Iz(_11e,_11f,_11n,_11w);});}};if(_11g>=_11f){return new F(function(){return _11k(_11f,_11g);});}else{return new F(function(){return _11k(_11g,_11f);});}};if(_11e>=_11g){return B(_11h(_11g,_11e));}else{return B(_11h(_11e,_11g));}}),_11x=new T(function(){var _11y=E(_118),_11z=E(_11y.a),_11A=E(_11y.b),_11B=E(_11c),_11C=E(_11B.a),_11D=E(_11B.b);return B(_Xl(new T(function(){return E(E(_115).a);},1),new T2(0,E(_11z),E(_11D)),_119,B(_NN(_11z.a,_11z.b,_11z.c,_11A.a,_11A.b,_11A.c,_11C.a,_11C.b,_11C.c,_11D.a,_11D.b,_11D.c,_11a,_10D))));}),_11E=new T(function(){var _11F=B(_UV(_118,_11a,_10D)),_11G=E(_11F.a),_11H=_11G.a,_11I=_11G.b,_11J=_11G.c,_11K=E(_11F.b).a,_11L=B(_VY(_11c,_11a,_10D)),_11M=E(_11L.a).a,_11N=E(_11L.b),_11O=_11N.a,_11P=_11N.b,_11Q=_11N.c,_11R=new T(function(){var _11S=new T(function(){return E(E(_10U).f);}),_11T=new T(function(){return E(E(_10U).d);}),_11U=new T(function(){return E(E(_10U).b);}),_11V=function(_11W){return (E(_11M)==0)?(E(_11O)==0)?new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11H,_11U,_11T),_6)):new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11H,_11U,_11T),new T2(1,new T3(0,_11T,_11S,_11O),_6))):new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11H,_11U,_11T),new T2(1,new T3(0,_11T,_11S,_11O),_6)));};if(!E(_11H)){if(!E(_11K)){return new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11T,_11S,_11O),_6));}else{return B(_11V(_));}}else{return B(_11V(_));}}),_11X=function(_11Y){return new F(function(){return _Qj(_wm,new T(function(){return E(E(_11Y).b);}),_11R);});},_11Z=B(_TG(_10I,B(_Sk(_11X,_10I)))),_120=function(_121){var _122=function(_123){var _124=function(_125){var _126=E(_125);if(!_126._){return E(_11Z);}else{var _127=E(_126.a);return new F(function(){return _K2(_Iy,new T3(0,_127.d,new T3(0,E(_127.a).a,E(_127.b).a,E(_127.c).a),_127),B(_124(_126.b)));});}};return new F(function(){return _124(B(_Q4(new T2(1,new T(function(){var _128=E(_116),_129=E(_11b);return B(_Lk(_Z8,_128.a,_128.b,_128.c,_129.a,_129.b,_129.c,_11O,_11P,_11Q));}),new T2(1,new T(function(){var _12a=E(_116),_12b=E(_11b);return B(_Lk(_Z8,_11H,_11I,_11J,_12a.a,_12a.b,_12a.c,_12b.a,_12b.b,_12b.c));}),_6)))));});};if(!E(_11M)){if(!E(_11O)){var _12c=E(_116),_12d=E(_11b),_12e=B(_Lk(_Z8,_11H,_11I,_11J,_12c.a,_12c.b,_12c.c,_12d.a,_12d.b,_12d.c));if(!_12e._){return E(_11Z);}else{return new F(function(){return _XL(_12e.a,_11Z);});}}else{return new F(function(){return _122(_);});}}else{return new F(function(){return _122(_);});}};if(!E(_11H)){if(!E(_11K)){var _12f=E(_116),_12g=E(_11b),_12h=B(_Lk(_Z8,_12f.a,_12f.b,_12f.c,_12g.a,_12g.b,_12g.c,_11O,_11P,_11Q));if(!_12h._){return E(_11Z);}else{return B(_XL(_12h.a,_11Z));}}else{return B(_120(_));}}else{return B(_120(_));}});return new T2(0,new T4(0,new T2(0,_10H,_11E),_11x,_11d,_119),_10S);},_12i=E(_10H);if(!_12i._){return new F(function(){return _10Q(_);});}else{var _12j=_12i.a,_12k=function(_12l){var _12m=new T(function(){var _12n=E(_12j);return new T3(0,_12n,_12n.a,_12n.c);}),_12o=new T(function(){return E(E(_12m).c);}),_12p=new T(function(){return E(E(_12m).a);}),_12q=new T(function(){var _12r=E(_12p),_12s=B(_OQ(_12r.a,_12r.b,_12r.c,_12o,_10D));return new T2(0,_12s.a,_12s.b);}),_12t=new T(function(){return E(E(_12q).b);}),_12u=new T(function(){var _12v=E(_12t);if(!_12v._){return E(E(_12v.a).a);}else{return E(E(_12v.a).b);}}),_12w=new T(function(){var _12x=function(_12y,_12z){var _12A=E(_12y),_12B=E(_12A.a);if(!E(_12B.a)){if(!E(E(_12A.b).a)){var _12C=__Z;}else{var _12C=new T1(1,new T3(0,0,_12B.b,_12B.c));}var _12D=_12C;}else{var _12D=new T1(1,_12B);}var _12E=new T(function(){var _12F=E(_12z),_12G=E(_12F.b);if(!E(E(_12F.a).a)){if(!E(_12G.a)){return __Z;}else{return new T1(1,_12G);}}else{return new T1(1,_12G);}}),_12H=E(_12D);if(!_12H._){var _12I=E(_10I);}else{var _12J=E(_12E);if(!_12J._){var _12K=E(_10I);}else{var _12L=new T(function(){return E(_12J.a).a;}),_12K=B(_TA(_10I,B(_Sk(function(_12M){var _12N=E(E(_12M).b);if(E(_12N.a)!=E(_12H.a).a){return false;}else{if(E(_12N.b)!=E(_12u).a){return false;}else{return new F(function(){return _w7(_12N.c,_12L);});}}},_10I))));}var _12I=_12K;}var _12O=function(_12P){var _12Q=E(_12P);if(!_12Q._){return E(_12I);}else{var _12R=E(_12Q.a);return new F(function(){return _K2(_Iy,new T3(0,_12R.d,new T3(0,E(_12R.a).a,E(_12R.b).a,E(_12R.c).a),_12R),B(_12O(_12Q.b)));});}};return new F(function(){return _12O(B(_Q4(new T2(1,new T(function(){var _12S=E(_12D);if(!_12S._){return __Z;}else{return B(_Qb(_Z8,_12S.a,_12u,_12p));}}),new T2(1,new T(function(){var _12T=E(_12E);if(!_12T._){return __Z;}else{return B(_Qb(_Z8,_12p,_12u,_12T.a));}}),_6)))));});},_12U=E(_12t);if(!_12U._){var _12V=_12U.a;return B(_12x(new T(function(){return B(_UV(_12V,_12o,_10D));}),_12V));}else{var _12W=_12U.a;return B(_12x(_12W,new T(function(){return B(_VY(_12W,_12o,_10D));})));}});return new T2(0,new T4(0,new T2(0,_12i.b,_12w),new T(function(){return E(E(_12q).a);}),new T(function(){var _12X=E(E(_12m).b),_12Y=E(_12u).a;if(_12X>=_12Y){return B(_Iz(_12Y,_12X,_Q3,_10E));}else{return B(_Iz(_12X,_12Y,_Q3,_10E));}}),_12o),new T(function(){var _12Z=E(_10F);return new T5(0,1,E(_12Z),new T4(0,_5i,_10E,_10D,_Y0),E(_wq),E(_wq));}));};if(!E(_10I)._){if(E(E(_10N).a)>E(_12j).c){return new F(function(){return _12k(_);});}else{return new F(function(){return _10Q(_);});}}else{return new F(function(){return _12k(_);});}}};if(!E(_10H)._){if(!E(_10I)._){var _130=B(_10L(_));return new T2(0,_130.a,_130.b);}else{return new T2(0,_10C,_wq);}}else{var _131=B(_10L(_));return new T2(0,_131.a,_131.b);}}),_132=B(_10x(new T(function(){return E(E(_10K).a);}),new T(function(){return B(_Ax(_10z,E(_10K).b));}),_));return new T2(0,_132.a,_132.b);});if(!E(_10H)._){if(!E(_10I)._){return E(_10J);}else{return new T2(0,new T(function(){return B(_Z9(_6,_10E));}),_wq);}}else{return E(_10J);}});return new T2(0,new T(function(){return E(E(_10B).a);}),new T(function(){return B(_Ax(_10z,E(_10B).b));}));},_133=new T(function(){return B(_SD(_Y6,new T(function(){return B(_Y7(_Yd,B(_Yg(_XQ,B(_Y7(_XV,_Z6))))));},1)));}),_134=new T(function(){var _135=B(_oU(_133,0));return new T3(0,_135,_135.a,_135.b);}),_136=new T(function(){var _137=B(_oU(_133,1));return new T4(0,_137,_137.a,_137.b,_137.c);}),_138=new T(function(){return E(E(_134).a);}),_139=new T(function(){return E(E(_136).a);}),_13a=new T3(1,_ON,new T(function(){return new T2(0,E(_138),E(_139));}),new T3(1,_ON,new T(function(){return new T2(0,E(_139),E(_138));}),_ON)),_13b=new T(function(){var _13c=E(E(_134).b),_13d=E(E(_136).b);if(_13c>=_13d){return new T5(0,1,E(new T2(0,_13d,_13c)),_Q3,E(_wq),E(_wq));}else{return new T5(0,1,E(new T2(0,_13c,_13d)),_Q3,E(_wq),E(_wq));}}),_13e=new T(function(){var _13f=E(_133);if(!_13f._){return E(_Yc);}else{var _13g=E(_13f.b);if(!_13g._){return E(_Yc);}else{var _13h=E(_13g.b);if(!_13h._){return new T2(0,new T(function(){return B(_Z9(_6,_13b));}),_wq);}else{var _13i=new T(function(){var _13j=E(_13h.a);return new T3(0,_13j,_13j.a,_13j.c);}),_13k=new T(function(){return E(E(_13i).c);}),_13l=new T(function(){return E(E(_13i).a);}),_13m=new T(function(){var _13n=E(_13l),_13o=B(_OQ(_13n.a,_13n.b,_13n.c,_13k,_13a));return new T2(0,_13o.a,_13o.b);}),_13p=new T(function(){return E(E(_13m).b);}),_13q=new T(function(){var _13r=E(_13p);if(!_13r._){return E(E(_13r.a).a);}else{return E(E(_13r.a).b);}}),_13s=new T(function(){var _13t=function(_13u,_13v){var _13w=E(_13u),_13x=E(_13w.a);if(!E(_13x.a)){if(!E(E(_13w.b).a)){var _13y=__Z;}else{var _13y=new T1(1,new T3(0,0,_13x.b,_13x.c));}var _13z=_13y;}else{var _13z=new T1(1,_13x);}var _13A=new T(function(){var _13B=E(_13v),_13C=E(_13B.b);if(!E(E(_13B.a).a)){if(!E(_13C.a)){return __Z;}else{return new T1(1,_13C);}}else{return new T1(1,_13C);}}),_13D=E(_13z);if(!_13D._){var _13E=new T0(1);}else{var _13F=E(_13A);if(!_13F._){var _13G=new T0(1);}else{var _13H=new T(function(){return E(_13F.a).a;}),_13G=B(_TA(_IL,B(_Sk(function(_13I){var _13J=E(E(_13I).b);if(E(_13J.a)!=E(_13D.a).a){return false;}else{if(E(_13J.b)!=E(_13q).a){return false;}else{return new F(function(){return _w7(_13J.c,_13H);});}}},_IL))));}var _13E=_13G;}var _13K=function(_13L){var _13M=E(_13L);if(!_13M._){return E(_13E);}else{var _13N=E(_13M.a);return new F(function(){return _K2(_Iy,new T3(0,_13N.d,new T3(0,E(_13N.a).a,E(_13N.b).a,E(_13N.c).a),_13N),B(_13K(_13M.b)));});}};return new F(function(){return _13K(B(_Q4(new T2(1,new T(function(){var _13O=E(_13z);if(!_13O._){return __Z;}else{return B(_Qb(_Z8,_13O.a,_13q,_13l));}}),new T2(1,new T(function(){var _13P=E(_13A);if(!_13P._){return __Z;}else{return B(_Qb(_Z8,_13l,_13q,_13P.a));}}),_6)))));});},_13Q=E(_13p);if(!_13Q._){var _13R=_13Q.a;return B(_13t(new T(function(){return B(_UV(_13R,_13k,_13a));}),_13R));}else{var _13S=_13Q.a;return B(_13t(_13S,new T(function(){return B(_VY(_13S,_13k,_13a));})));}}),_13T=B(_10x(new T4(0,new T2(0,_13h.b,_13s),new T(function(){return E(E(_13m).a);}),new T(function(){var _13U=E(E(_13i).b),_13V=E(_13q).a;if(_13U>=_13V){return B(_Iz(_13V,_13U,_Q3,_13b));}else{return B(_Iz(_13U,_13V,_Q3,_13b));}}),_13k),new T(function(){var _13W=E(E(_136).d);return new T5(0,1,E(_13W),new T4(0,_5i,_13b,_13a,_Y0),E(_wq),E(_wq));}),_));return new T2(0,_13T.a,_13T.b);}}}});return new T2(0,new T(function(){return E(E(_13e).a);}),new T(function(){return B(_Ax(_wq,E(_13e).b));}));},_13X=function(_13Y,_13Z){return (!E(_13Y))?false:E(_13Z);},_140=1,_141=function(_142){return new T1(1,_142);},_143=1,_144=new T(function(){return eval("(function(){return Util.height;})");}),_145=new T(function(){return eval("(function(){return Util.width;})");}),_146=function(_){var _147=E(_4r),_148=__app1(E(_145),_147),_149=__app1(E(_144),_147);return new T2(0,_148,_149);},_14a=function(_){var _14b=B(_146(_));return new T(function(){return E(E(_14b).a)/2;});},_14c=new T1(1,_14a),_14d=new T1(0,_ac),_14e=function(_14f,_14g,_14h,_14i,_){var _14j=function(_,_14k){var _14l=function(_,_14m){var _14n=function(_,_14o){var _14p=E(_14i);switch(_14p._){case 0:return new T(function(){var _14q=function(_14r){var _14s=_14r*256,_14t=_14s&4294967295,_14u=function(_14v){var _14w=E(_14m)*256,_14x=_14w&4294967295,_14y=function(_14z){var _14A=function(_14B){var _14C=_14B*256,_14D=_14C&4294967295,_14E=function(_14F){var _14G=E(_14p.a);return (1>_14G)?(0>_14G)?new T4(1,_14v,_14z,_14F,0):new T4(1,_14v,_14z,_14F,_14G):new T4(1,_14v,_14z,_14F,1);};if(_14C>=_14D){if(255>_14D){if(0>_14D){return new F(function(){return _14E(0);});}else{return new F(function(){return _14E(_14D);});}}else{return new F(function(){return _14E(255);});}}else{var _14H=_14D-1|0;if(255>_14H){if(0>_14H){return new F(function(){return _14E(0);});}else{return new F(function(){return _14E(_14H);});}}else{return new F(function(){return _14E(255);});}}},_14I=E(_14o);if(!_14I._){return new F(function(){return _14A(0);});}else{return new F(function(){return _14A(E(_14I.a));});}};if(_14w>=_14x){if(255>_14x){if(0>_14x){return new F(function(){return _14y(0);});}else{return new F(function(){return _14y(_14x);});}}else{return new F(function(){return _14y(255);});}}else{var _14J=_14x-1|0;if(255>_14J){if(0>_14J){return new F(function(){return _14y(0);});}else{return new F(function(){return _14y(_14J);});}}else{return new F(function(){return _14y(255);});}}};if(_14s>=_14t){if(255>_14t){if(0>_14t){return new F(function(){return _14u(0);});}else{return new F(function(){return _14u(_14t);});}}else{return new F(function(){return _14u(255);});}}else{var _14K=_14t-1|0;if(255>_14K){if(0>_14K){return new F(function(){return _14u(0);});}else{return new F(function(){return _14u(_14K);});}}else{return new F(function(){return _14u(255);});}}},_14L=E(_14k);if(!_14L._){return B(_14q(0));}else{return B(_14q(E(_14L.a)));}});case 1:var _14M=B(A1(_14p.a,_)),_14N=_14M;return new T(function(){var _14O=function(_14P){var _14Q=_14P*256,_14R=_14Q&4294967295,_14S=function(_14T){var _14U=E(_14m)*256,_14V=_14U&4294967295,_14W=function(_14X){var _14Y=function(_14Z){var _150=_14Z*256,_151=_150&4294967295,_152=function(_153){var _154=E(_14N);return (1>_154)?(0>_154)?new T4(1,_14T,_14X,_153,0):new T4(1,_14T,_14X,_153,_154):new T4(1,_14T,_14X,_153,1);};if(_150>=_151){if(255>_151){if(0>_151){return new F(function(){return _152(0);});}else{return new F(function(){return _152(_151);});}}else{return new F(function(){return _152(255);});}}else{var _155=_151-1|0;if(255>_155){if(0>_155){return new F(function(){return _152(0);});}else{return new F(function(){return _152(_155);});}}else{return new F(function(){return _152(255);});}}},_156=E(_14o);if(!_156._){return new F(function(){return _14Y(0);});}else{return new F(function(){return _14Y(E(_156.a));});}};if(_14U>=_14V){if(255>_14V){if(0>_14V){return new F(function(){return _14W(0);});}else{return new F(function(){return _14W(_14V);});}}else{return new F(function(){return _14W(255);});}}else{var _157=_14V-1|0;if(255>_157){if(0>_157){return new F(function(){return _14W(0);});}else{return new F(function(){return _14W(_157);});}}else{return new F(function(){return _14W(255);});}}};if(_14Q>=_14R){if(255>_14R){if(0>_14R){return new F(function(){return _14S(0);});}else{return new F(function(){return _14S(_14R);});}}else{return new F(function(){return _14S(255);});}}else{var _158=_14R-1|0;if(255>_158){if(0>_158){return new F(function(){return _14S(0);});}else{return new F(function(){return _14S(_158);});}}else{return new F(function(){return _14S(255);});}}},_159=E(_14k);if(!_159._){return B(_14O(0));}else{return B(_14O(E(_159.a)));}});case 2:var _15a=rMV(E(E(_14p.a).c)),_15b=E(_15a);return (_15b._==0)?new T(function(){var _15c=function(_15d){var _15e=_15d*256,_15f=_15e&4294967295,_15g=function(_15h){var _15i=E(_14m)*256,_15j=_15i&4294967295,_15k=function(_15l){var _15m=function(_15n){var _15o=_15n*256,_15p=_15o&4294967295,_15q=function(_15r){var _15s=B(A1(_14p.b,new T(function(){return B(_qq(_15b.a));})));return (1>_15s)?(0>_15s)?new T4(1,_15h,_15l,_15r,0):new T4(1,_15h,_15l,_15r,_15s):new T4(1,_15h,_15l,_15r,1);};if(_15o>=_15p){if(255>_15p){if(0>_15p){return new F(function(){return _15q(0);});}else{return new F(function(){return _15q(_15p);});}}else{return new F(function(){return _15q(255);});}}else{var _15t=_15p-1|0;if(255>_15t){if(0>_15t){return new F(function(){return _15q(0);});}else{return new F(function(){return _15q(_15t);});}}else{return new F(function(){return _15q(255);});}}},_15u=E(_14o);if(!_15u._){return new F(function(){return _15m(0);});}else{return new F(function(){return _15m(E(_15u.a));});}};if(_15i>=_15j){if(255>_15j){if(0>_15j){return new F(function(){return _15k(0);});}else{return new F(function(){return _15k(_15j);});}}else{return new F(function(){return _15k(255);});}}else{var _15v=_15j-1|0;if(255>_15v){if(0>_15v){return new F(function(){return _15k(0);});}else{return new F(function(){return _15k(_15v);});}}else{return new F(function(){return _15k(255);});}}};if(_15e>=_15f){if(255>_15f){if(0>_15f){return new F(function(){return _15g(0);});}else{return new F(function(){return _15g(_15f);});}}else{return new F(function(){return _15g(255);});}}else{var _15w=_15f-1|0;if(255>_15w){if(0>_15w){return new F(function(){return _15g(0);});}else{return new F(function(){return _15g(_15w);});}}else{return new F(function(){return _15g(255);});}}},_15x=E(_14k);if(!_15x._){return B(_15c(0));}else{return B(_15c(E(_15x.a)));}}):new T(function(){var _15y=function(_15z){var _15A=_15z*256,_15B=_15A&4294967295,_15C=function(_15D){var _15E=E(_14m)*256,_15F=_15E&4294967295,_15G=function(_15H){var _15I=function(_15J){var _15K=_15J*256,_15L=_15K&4294967295;if(_15K>=_15L){return (255>_15L)?(0>_15L)?new T4(1,_15D,_15H,0,1):new T4(1,_15D,_15H,_15L,1):new T4(1,_15D,_15H,255,1);}else{var _15M=_15L-1|0;return (255>_15M)?(0>_15M)?new T4(1,_15D,_15H,0,1):new T4(1,_15D,_15H,_15M,1):new T4(1,_15D,_15H,255,1);}},_15N=E(_14o);if(!_15N._){return new F(function(){return _15I(0);});}else{return new F(function(){return _15I(E(_15N.a));});}};if(_15E>=_15F){if(255>_15F){if(0>_15F){return new F(function(){return _15G(0);});}else{return new F(function(){return _15G(_15F);});}}else{return new F(function(){return _15G(255);});}}else{var _15O=_15F-1|0;if(255>_15O){if(0>_15O){return new F(function(){return _15G(0);});}else{return new F(function(){return _15G(_15O);});}}else{return new F(function(){return _15G(255);});}}};if(_15A>=_15B){if(255>_15B){if(0>_15B){return new F(function(){return _15C(0);});}else{return new F(function(){return _15C(_15B);});}}else{return new F(function(){return _15C(255);});}}else{var _15P=_15B-1|0;if(255>_15P){if(0>_15P){return new F(function(){return _15C(0);});}else{return new F(function(){return _15C(_15P);});}}else{return new F(function(){return _15C(255);});}}},_15Q=E(_14k);if(!_15Q._){return B(_15y(0));}else{return B(_15y(E(_15Q.a)));}});default:var _15R=rMV(E(E(_14p.a).c)),_15S=E(_15R);if(!_15S._){var _15T=B(A2(_14p.b,E(_15S.a).a,_)),_15U=_15T;return new T(function(){var _15V=function(_15W){var _15X=_15W*256,_15Y=_15X&4294967295,_15Z=function(_160){var _161=E(_14m)*256,_162=_161&4294967295,_163=function(_164){var _165=function(_166){var _167=_166*256,_168=_167&4294967295,_169=function(_16a){var _16b=E(_15U);return (1>_16b)?(0>_16b)?new T4(1,_160,_164,_16a,0):new T4(1,_160,_164,_16a,_16b):new T4(1,_160,_164,_16a,1);};if(_167>=_168){if(255>_168){if(0>_168){return new F(function(){return _169(0);});}else{return new F(function(){return _169(_168);});}}else{return new F(function(){return _169(255);});}}else{var _16c=_168-1|0;if(255>_16c){if(0>_16c){return new F(function(){return _169(0);});}else{return new F(function(){return _169(_16c);});}}else{return new F(function(){return _169(255);});}}},_16d=E(_14o);if(!_16d._){return new F(function(){return _165(0);});}else{return new F(function(){return _165(E(_16d.a));});}};if(_161>=_162){if(255>_162){if(0>_162){return new F(function(){return _163(0);});}else{return new F(function(){return _163(_162);});}}else{return new F(function(){return _163(255);});}}else{var _16e=_162-1|0;if(255>_16e){if(0>_16e){return new F(function(){return _163(0);});}else{return new F(function(){return _163(_16e);});}}else{return new F(function(){return _163(255);});}}};if(_15X>=_15Y){if(255>_15Y){if(0>_15Y){return new F(function(){return _15Z(0);});}else{return new F(function(){return _15Z(_15Y);});}}else{return new F(function(){return _15Z(255);});}}else{var _16f=_15Y-1|0;if(255>_16f){if(0>_16f){return new F(function(){return _15Z(0);});}else{return new F(function(){return _15Z(_16f);});}}else{return new F(function(){return _15Z(255);});}}},_16g=E(_14k);if(!_16g._){return B(_15V(0));}else{return B(_15V(E(_16g.a)));}});}else{return new T(function(){var _16h=function(_16i){var _16j=_16i*256,_16k=_16j&4294967295,_16l=function(_16m){var _16n=E(_14m)*256,_16o=_16n&4294967295,_16p=function(_16q){var _16r=function(_16s){var _16t=_16s*256,_16u=_16t&4294967295;if(_16t>=_16u){return (255>_16u)?(0>_16u)?new T4(1,_16m,_16q,0,1):new T4(1,_16m,_16q,_16u,1):new T4(1,_16m,_16q,255,1);}else{var _16v=_16u-1|0;return (255>_16v)?(0>_16v)?new T4(1,_16m,_16q,0,1):new T4(1,_16m,_16q,_16v,1):new T4(1,_16m,_16q,255,1);}},_16w=E(_14o);if(!_16w._){return new F(function(){return _16r(0);});}else{return new F(function(){return _16r(E(_16w.a));});}};if(_16n>=_16o){if(255>_16o){if(0>_16o){return new F(function(){return _16p(0);});}else{return new F(function(){return _16p(_16o);});}}else{return new F(function(){return _16p(255);});}}else{var _16x=_16o-1|0;if(255>_16x){if(0>_16x){return new F(function(){return _16p(0);});}else{return new F(function(){return _16p(_16x);});}}else{return new F(function(){return _16p(255);});}}};if(_16j>=_16k){if(255>_16k){if(0>_16k){return new F(function(){return _16l(0);});}else{return new F(function(){return _16l(_16k);});}}else{return new F(function(){return _16l(255);});}}else{var _16y=_16k-1|0;if(255>_16y){if(0>_16y){return new F(function(){return _16l(0);});}else{return new F(function(){return _16l(_16y);});}}else{return new F(function(){return _16l(255);});}}},_16z=E(_14k);if(!_16z._){return B(_16h(0));}else{return B(_16h(E(_16z.a)));}});}}},_16A=E(_14h);switch(_16A._){case 0:return new F(function(){return _14n(_,new T1(1,_16A.a));});break;case 1:var _16B=B(A1(_16A.a,_));return new F(function(){return _14n(_,new T1(1,_16B));});break;case 2:var _16C=rMV(E(E(_16A.a).c)),_16D=E(_16C);if(!_16D._){var _16E=new T(function(){return B(A1(_16A.b,new T(function(){return B(_qq(_16D.a));})));});return new F(function(){return _14n(_,new T1(1,_16E));});}else{return new F(function(){return _14n(_,_2o);});}break;default:var _16F=rMV(E(E(_16A.a).c)),_16G=E(_16F);if(!_16G._){var _16H=B(A2(_16A.b,E(_16G.a).a,_));return new F(function(){return _14n(_,new T1(1,_16H));});}else{return new F(function(){return _14n(_,_2o);});}}},_16I=function(_){var _16J=function(_,_16K){var _16L=E(_14i);switch(_16L._){case 0:return new T(function(){var _16M=function(_16N){var _16O=_16N*256,_16P=_16O&4294967295,_16Q=function(_16R){var _16S=function(_16T){var _16U=_16T*256,_16V=_16U&4294967295,_16W=function(_16X){var _16Y=E(_16L.a);return (1>_16Y)?(0>_16Y)?new T4(1,_16R,0,_16X,0):new T4(1,_16R,0,_16X,_16Y):new T4(1,_16R,0,_16X,1);};if(_16U>=_16V){if(255>_16V){if(0>_16V){return new F(function(){return _16W(0);});}else{return new F(function(){return _16W(_16V);});}}else{return new F(function(){return _16W(255);});}}else{var _16Z=_16V-1|0;if(255>_16Z){if(0>_16Z){return new F(function(){return _16W(0);});}else{return new F(function(){return _16W(_16Z);});}}else{return new F(function(){return _16W(255);});}}},_170=E(_16K);if(!_170._){return new F(function(){return _16S(0);});}else{return new F(function(){return _16S(E(_170.a));});}};if(_16O>=_16P){if(255>_16P){if(0>_16P){return new F(function(){return _16Q(0);});}else{return new F(function(){return _16Q(_16P);});}}else{return new F(function(){return _16Q(255);});}}else{var _171=_16P-1|0;if(255>_171){if(0>_171){return new F(function(){return _16Q(0);});}else{return new F(function(){return _16Q(_171);});}}else{return new F(function(){return _16Q(255);});}}},_172=E(_14k);if(!_172._){return B(_16M(0));}else{return B(_16M(E(_172.a)));}});case 1:var _173=B(A1(_16L.a,_)),_174=_173;return new T(function(){var _175=function(_176){var _177=_176*256,_178=_177&4294967295,_179=function(_17a){var _17b=function(_17c){var _17d=_17c*256,_17e=_17d&4294967295,_17f=function(_17g){var _17h=E(_174);return (1>_17h)?(0>_17h)?new T4(1,_17a,0,_17g,0):new T4(1,_17a,0,_17g,_17h):new T4(1,_17a,0,_17g,1);};if(_17d>=_17e){if(255>_17e){if(0>_17e){return new F(function(){return _17f(0);});}else{return new F(function(){return _17f(_17e);});}}else{return new F(function(){return _17f(255);});}}else{var _17i=_17e-1|0;if(255>_17i){if(0>_17i){return new F(function(){return _17f(0);});}else{return new F(function(){return _17f(_17i);});}}else{return new F(function(){return _17f(255);});}}},_17j=E(_16K);if(!_17j._){return new F(function(){return _17b(0);});}else{return new F(function(){return _17b(E(_17j.a));});}};if(_177>=_178){if(255>_178){if(0>_178){return new F(function(){return _179(0);});}else{return new F(function(){return _179(_178);});}}else{return new F(function(){return _179(255);});}}else{var _17k=_178-1|0;if(255>_17k){if(0>_17k){return new F(function(){return _179(0);});}else{return new F(function(){return _179(_17k);});}}else{return new F(function(){return _179(255);});}}},_17l=E(_14k);if(!_17l._){return B(_175(0));}else{return B(_175(E(_17l.a)));}});case 2:var _17m=rMV(E(E(_16L.a).c)),_17n=E(_17m);return (_17n._==0)?new T(function(){var _17o=function(_17p){var _17q=_17p*256,_17r=_17q&4294967295,_17s=function(_17t){var _17u=function(_17v){var _17w=_17v*256,_17x=_17w&4294967295,_17y=function(_17z){var _17A=B(A1(_16L.b,new T(function(){return B(_qq(_17n.a));})));return (1>_17A)?(0>_17A)?new T4(1,_17t,0,_17z,0):new T4(1,_17t,0,_17z,_17A):new T4(1,_17t,0,_17z,1);};if(_17w>=_17x){if(255>_17x){if(0>_17x){return new F(function(){return _17y(0);});}else{return new F(function(){return _17y(_17x);});}}else{return new F(function(){return _17y(255);});}}else{var _17B=_17x-1|0;if(255>_17B){if(0>_17B){return new F(function(){return _17y(0);});}else{return new F(function(){return _17y(_17B);});}}else{return new F(function(){return _17y(255);});}}},_17C=E(_16K);if(!_17C._){return new F(function(){return _17u(0);});}else{return new F(function(){return _17u(E(_17C.a));});}};if(_17q>=_17r){if(255>_17r){if(0>_17r){return new F(function(){return _17s(0);});}else{return new F(function(){return _17s(_17r);});}}else{return new F(function(){return _17s(255);});}}else{var _17D=_17r-1|0;if(255>_17D){if(0>_17D){return new F(function(){return _17s(0);});}else{return new F(function(){return _17s(_17D);});}}else{return new F(function(){return _17s(255);});}}},_17E=E(_14k);if(!_17E._){return B(_17o(0));}else{return B(_17o(E(_17E.a)));}}):new T(function(){var _17F=function(_17G){var _17H=_17G*256,_17I=_17H&4294967295,_17J=function(_17K){var _17L=function(_17M){var _17N=_17M*256,_17O=_17N&4294967295;if(_17N>=_17O){return (255>_17O)?(0>_17O)?new T4(1,_17K,0,0,1):new T4(1,_17K,0,_17O,1):new T4(1,_17K,0,255,1);}else{var _17P=_17O-1|0;return (255>_17P)?(0>_17P)?new T4(1,_17K,0,0,1):new T4(1,_17K,0,_17P,1):new T4(1,_17K,0,255,1);}},_17Q=E(_16K);if(!_17Q._){return new F(function(){return _17L(0);});}else{return new F(function(){return _17L(E(_17Q.a));});}};if(_17H>=_17I){if(255>_17I){if(0>_17I){return new F(function(){return _17J(0);});}else{return new F(function(){return _17J(_17I);});}}else{return new F(function(){return _17J(255);});}}else{var _17R=_17I-1|0;if(255>_17R){if(0>_17R){return new F(function(){return _17J(0);});}else{return new F(function(){return _17J(_17R);});}}else{return new F(function(){return _17J(255);});}}},_17S=E(_14k);if(!_17S._){return B(_17F(0));}else{return B(_17F(E(_17S.a)));}});default:var _17T=rMV(E(E(_16L.a).c)),_17U=E(_17T);if(!_17U._){var _17V=B(A2(_16L.b,E(_17U.a).a,_)),_17W=_17V;return new T(function(){var _17X=function(_17Y){var _17Z=_17Y*256,_180=_17Z&4294967295,_181=function(_182){var _183=function(_184){var _185=_184*256,_186=_185&4294967295,_187=function(_188){var _189=E(_17W);return (1>_189)?(0>_189)?new T4(1,_182,0,_188,0):new T4(1,_182,0,_188,_189):new T4(1,_182,0,_188,1);};if(_185>=_186){if(255>_186){if(0>_186){return new F(function(){return _187(0);});}else{return new F(function(){return _187(_186);});}}else{return new F(function(){return _187(255);});}}else{var _18a=_186-1|0;if(255>_18a){if(0>_18a){return new F(function(){return _187(0);});}else{return new F(function(){return _187(_18a);});}}else{return new F(function(){return _187(255);});}}},_18b=E(_16K);if(!_18b._){return new F(function(){return _183(0);});}else{return new F(function(){return _183(E(_18b.a));});}};if(_17Z>=_180){if(255>_180){if(0>_180){return new F(function(){return _181(0);});}else{return new F(function(){return _181(_180);});}}else{return new F(function(){return _181(255);});}}else{var _18c=_180-1|0;if(255>_18c){if(0>_18c){return new F(function(){return _181(0);});}else{return new F(function(){return _181(_18c);});}}else{return new F(function(){return _181(255);});}}},_18d=E(_14k);if(!_18d._){return B(_17X(0));}else{return B(_17X(E(_18d.a)));}});}else{return new T(function(){var _18e=function(_18f){var _18g=_18f*256,_18h=_18g&4294967295,_18i=function(_18j){var _18k=function(_18l){var _18m=_18l*256,_18n=_18m&4294967295;if(_18m>=_18n){return (255>_18n)?(0>_18n)?new T4(1,_18j,0,0,1):new T4(1,_18j,0,_18n,1):new T4(1,_18j,0,255,1);}else{var _18o=_18n-1|0;return (255>_18o)?(0>_18o)?new T4(1,_18j,0,0,1):new T4(1,_18j,0,_18o,1):new T4(1,_18j,0,255,1);}},_18p=E(_16K);if(!_18p._){return new F(function(){return _18k(0);});}else{return new F(function(){return _18k(E(_18p.a));});}};if(_18g>=_18h){if(255>_18h){if(0>_18h){return new F(function(){return _18i(0);});}else{return new F(function(){return _18i(_18h);});}}else{return new F(function(){return _18i(255);});}}else{var _18q=_18h-1|0;if(255>_18q){if(0>_18q){return new F(function(){return _18i(0);});}else{return new F(function(){return _18i(_18q);});}}else{return new F(function(){return _18i(255);});}}},_18r=E(_14k);if(!_18r._){return B(_18e(0));}else{return B(_18e(E(_18r.a)));}});}}},_18s=E(_14h);switch(_18s._){case 0:return new F(function(){return _16J(_,new T1(1,_18s.a));});break;case 1:var _18t=B(A1(_18s.a,_));return new F(function(){return _16J(_,new T1(1,_18t));});break;case 2:var _18u=rMV(E(E(_18s.a).c)),_18v=E(_18u);if(!_18v._){var _18w=new T(function(){return B(A1(_18s.b,new T(function(){return B(_qq(_18v.a));})));});return new F(function(){return _16J(_,new T1(1,_18w));});}else{return new F(function(){return _16J(_,_2o);});}break;default:var _18x=rMV(E(E(_18s.a).c)),_18y=E(_18x);if(!_18y._){var _18z=B(A2(_18s.b,E(_18y.a).a,_));return new F(function(){return _16J(_,new T1(1,_18z));});}else{return new F(function(){return _16J(_,_2o);});}}},_18A=E(_14g);switch(_18A._){case 0:return new F(function(){return _14l(_,_18A.a);});break;case 1:var _18B=B(A1(_18A.a,_));return new F(function(){return _14l(_,_18B);});break;case 2:var _18C=rMV(E(E(_18A.a).c)),_18D=E(_18C);if(!_18D._){var _18E=new T(function(){return B(A1(_18A.b,new T(function(){return E(E(_18D.a).a);})));});return new F(function(){return _14l(_,_18E);});}else{return new F(function(){return _16I(_);});}break;default:var _18F=rMV(E(E(_18A.a).c)),_18G=E(_18F);if(!_18G._){var _18H=B(A2(_18A.b,E(_18G.a).a,_));return new F(function(){return _14l(_,_18H);});}else{return new F(function(){return _16I(_);});}}},_18I=E(_14f);switch(_18I._){case 0:return new F(function(){return _14j(_,new T1(1,_18I.a));});break;case 1:var _18J=B(A1(_18I.a,_));return new F(function(){return _14j(_,new T1(1,_18J));});break;case 2:var _18K=rMV(E(E(_18I.a).c)),_18L=E(_18K);if(!_18L._){var _18M=new T(function(){return B(A1(_18I.b,new T(function(){return B(_qq(_18L.a));})));});return new F(function(){return _14j(_,new T1(1,_18M));});}else{return new F(function(){return _14j(_,_2o);});}break;default:var _18N=rMV(E(E(_18I.a).c)),_18O=E(_18N);if(!_18O._){var _18P=B(A2(_18I.b,E(_18O.a).a,_));return new F(function(){return _14j(_,new T1(1,_18P));});}else{return new F(function(){return _14j(_,_2o);});}}},_18Q=")",_18R=new T2(1,_18Q,_6),_18S=",",_18T="rgba(",_18U=new T(function(){return toJSStr(_6);}),_18V="rgb(",_18W=function(_18X){var _18Y=E(_18X);if(!_18Y._){var _18Z=jsCat(new T2(1,_18V,new T2(1,new T(function(){return String(_18Y.a);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.b);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.c);}),_18R)))))),E(_18U));return E(_18Z);}else{var _190=jsCat(new T2(1,_18T,new T2(1,new T(function(){return String(_18Y.a);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.b);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.c);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.d);}),_18R)))))))),E(_18U));return E(_190);}},_191=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_192="fillStyle",_193=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_194=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_195=function(_196,_197){return new T2(1,new T2(0,function(_198,_){var _199=E(_196),_19a=B(_14e(_199.a,_199.b,_199.c,_199.d,_)),_19b=E(_198),_19c=__app3(E(_194),_19b,E(_192),B(_18W(_19a))),_19d=__app1(E(_191),_19b),_19e=B(A3(E(_197).b,_19b,_ch,_)),_19f=__app1(E(_193),_19b);return new F(function(){return _qQ(_);});},_7),_14d);},_19g=function(_19h,_19i,_19j,_19k){var _19l=function(_19m,_19n,_19o,_){var _19p=function(_19q,_19r,_19s,_){var _19t=function(_19u,_19v,_19w,_){return new F(function(){return _qs(_19k,function(_19x,_19y,_19z,_){var _19A=E(_19m),_19B=E(_19q),_19C=E(_19y),_19D=E(_19z),_19E=__app4(E(_qS),_19A,_19B,_19C,_19D),_19F=_19A+E(_19u),_19G=E(_uf),_19H=__app4(_19G,_19F,_19B,_19C,_19D),_19I=_19B+E(_19x),_19J=__app4(_19G,_19F,_19I,_19C,_19D),_19K=__app4(_19G,_19A,_19I,_19C,_19D),_19L=__app4(_19G,_19A,_19B,_19C,_19D);return new F(function(){return _qQ(_);});},_19v,_19w,_);});};return new F(function(){return _qs(_19j,_19t,_19r,_19s,_);});};return new F(function(){return _qs(_19i,_19p,_19n,_19o,_);});},_19M=function(_19N,_){var _19O=E(_19N),_19P=function(_19Q,_){var _19R=function(_19S,_){var _19T=function(_19U,_){var _19V=function(_19W,_){return new T(function(){var _19X=E(_19U),_19Y=E(_19O.a)-E(_19Q)-_19X/2,_19Z=function(_1a0){var _1a1=E(_19W),_1a2=E(_19O.b)-E(_19S)-_1a1/2;return (_1a2!=0)?(_1a2<=0)? -_1a2<_1a1/2:_1a2<_1a1/2:0<_1a1/2;};if(_19Y!=0){if(_19Y<=0){if( -_19Y>=_19X/2){return false;}else{return B(_19Z(_));}}else{if(_19Y>=_19X/2){return false;}else{return B(_19Z(_));}}}else{if(0>=_19X/2){return false;}else{return B(_19Z(_));}}});};return new F(function(){return _qF(_19k,_19V,_);});};return new F(function(){return _qF(_19j,_19T,_);});};return new F(function(){return _qF(_19i,_19R,_);});};return new F(function(){return _qF(_19h,_19P,_);});};return new T3(0,_19M,function(_ry,_rz,_){return new F(function(){return _qs(_19h,_19l,_ry,_rz,_);});},_7);},_1a3=function(_){var _1a4=B(_146(_));return new T(function(){return E(E(_1a4).b);});},_1a5=new T1(1,_1a3),_1a6=0,_1a7=new T1(0,_1a6),_1a8=new T(function(){var _1a9=B(_19g(_1a7,_1a7,_14c,_1a5));return new T3(0,_1a9.a,_1a9.b,_1a9.c);}),_1aa=1,_1ab=new T1(0,_1aa),_1ac=new T4(0,_1ab,_1ab,_1ab,_1ab),_1ad=new T(function(){return B(_195(_1ac,_1a8));}),_1ae=10,_1af=new T1(0,_6),_1ag=new T1(0,_ac),_1ah=new T(function(){return B(unCStr("head"));}),_1ai=new T(function(){return B(_eZ(_1ah));}),_1aj=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_1ak=function(_1al,_){var _1am=__app1(E(_1aj),E(_1al));return new F(function(){return _qQ(_);});},_1an=new T2(0,_1ak,_7),_1ao=new T2(1,_1an,_14d),_1ap=function(_1aq){return E(_1ao);},_1ar=new T1(0,_1ap),_1as=new T(function(){return eval("(function(ctx){ctx.clip();})");}),_1at=new T(function(){return eval("(function(ctx){ctx.save();})");}),_1au=function(_1av,_1aw){return new T2(1,new T2(0,function(_1ax,_){var _1ay=E(_1ax),_1az=__app1(E(_1at),_1ay),_1aA=__app1(E(_191),_1ay),_1aB=B(A3(E(_1av).b,_1ay,_ch,_)),_1aC=__app1(E(_1as),_1ay);return new F(function(){return _qQ(_);});},_7),new T2(1,new T2(1,_14d,new T1(0,function(_1aD){return E(_1aw);})),_1ar));},_1aE=function(_1aF){var _1aG=E(_1aF);if(!_1aG._){return __Z;}else{var _1aH=E(_1aG.b);return (_1aH._==0)?__Z:new T2(1,_1aH.a,new T(function(){return B(_1aE(_1aH.b));}));}},_1aI=function(_1aJ,_1aK){return new F(function(){return A1(_1aK,new T2(0,_7,_1aJ));});},_1aL=function(_1aM,_1aN,_1aO){return new F(function(){return _1aI(_1aN,_1aO);});},_1aP=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1aQ=new T(function(){return B(err(_1aP));}),_1aR=0,_1aS=0,_1aT=0.15,_1aU=new T1(0,_1aT),_1aV=1,_1aW=new T1(0,_1aV),_1aX=new T4(0,_1aU,_1aU,_1aU,_1aW),_1aY=new T2(1,_ex,_6),_1aZ=2,_1b0=new T1(0,_1aZ),_1b1=0.2,_1b2=new T1(0,_1b1),_1b3=new T4(0,_1a7,_1aW,_1b2,_1aW),_1b4="mplus",_1b5=new T1(0,_1ae),_1b6=function(_1b7,_1b8,_){var _1b9=E(_1b7);switch(_1b9._){case 0:return new F(function(){return A2(_1b8,_1b9.a,_);});break;case 1:var _1ba=B(A1(_1b9.a,_));return new F(function(){return A2(_1b8,_1ba,_);});break;case 2:var _1bb=rMV(E(E(_1b9.a).c)),_1bc=E(_1bb);if(!_1bc._){var _1bd=new T(function(){return B(A1(_1b9.b,new T(function(){return B(_qq(_1bc.a));})));});return new F(function(){return A2(_1b8,_1bd,_);});}else{return _7;}break;default:var _1be=rMV(E(E(_1b9.a).c)),_1bf=E(_1be);if(!_1bf._){var _1bg=B(A2(_1b9.b,E(_1bf.a).a,_));return new F(function(){return A2(_1b8,_1bg,_);});}else{return _7;}}},_1bh="lineWidth",_1bi="strokeStyle",_1bj=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_1bk=function(_1bl,_1bm,_1bn){var _1bo=function(_1bp,_){return new F(function(){return _1b6(_1bl,function(_1bq,_){var _1br=E(_1bm),_1bs=B(_14e(_1br.a,_1br.b,_1br.c,_1br.d,_)),_1bt=E(_1bp),_1bu=E(_194),_1bv=__app3(_1bu,_1bt,E(_1bi),B(_18W(_1bs))),_1bw=String(E(_1bq)),_1bx=__app3(_1bu,_1bt,E(_1bh),_1bw),_1by=__app1(E(_191),_1bt),_1bz=B(A3(E(_1bn).b,_1bt,_5i,_)),_1bA=__app1(E(_1bj),_1bt);return new F(function(){return _qQ(_);});},_);});};return new T2(1,new T2(0,_1bo,_7),_14d);},_1bB=function(_1bC){var _1bD=E(_1bC);if(!_1bD._){return E(_oI);}else{var _1bE=E(_1bD.a),_1bF=E(_1bE.c),_1bG=_1bF.a,_1bH=_1bF.b,_1bI=E(_1bE.d),_1bJ=new T(function(){return B(_1bB(_1bD.b));}),_1bK=function(_1bL){return E(_1bJ);},_1bM=new T(function(){var _1bN=new T(function(){var _1bO=new T(function(){return B(A3(_f3,_eT,new T2(1,function(_1bP){return new F(function(){return _fd(0,_1bE.a,_1bP);});},new T2(1,function(_1bQ){return new F(function(){return _fd(0,_1bE.b,_1bQ);});},_6)),_1aY));}),_1bR=B(_vh(_1b4,new T1(0,new T2(1,_ey,_1bO)),_1aR,_1aS,new T1(0,_1bG),new T1(0,_1bH),_1b5));return new T3(0,_1bR.a,_1bR.b,_1bR.c);});return B(_195(_1aX,_1bN));}),_1bS=B(_1bk(_1b0,_1b3,new T(function(){var _1bT=B(_um(new T2(0,new T1(0,_1bG),new T1(0,_1bH)),new T2(0,new T1(0,_1bI.a),new T1(0,_1bI.b))));return new T3(0,_1bT.a,_1bT.b,_1bT.c);})));if(!_1bS._){var _1bU=E(_1bM);return (_1bU._==0)?E(_1bJ):new T2(1,_1bU.a,new T2(1,_1bU.b,new T1(0,_1bK)));}else{return new T2(1,_1bS.a,new T2(1,new T2(1,_1bS.b,new T1(0,function(_1bV){return E(_1bM);})),new T1(0,_1bK)));}}},_1bW=function(_1bX){var _1bY=E(_1bX);if(!_1bY._){return __Z;}else{var _1bZ=E(_1bY.a);return new T2(1,_1bZ.a,new T2(1,_1bZ.b,new T(function(){return B(_1bW(_1bY.b));})));}},_1c0=new T4(0,_1aW,_1a7,_1a7,_1aW),_1c1=5,_1c2=new T1(0,_1c1),_1c3=function(_1c4,_1c5){while(1){var _1c6=B((function(_1c7,_1c8){var _1c9=E(_1c8);if(!_1c9._){var _1ca=_1c9.e,_1cb=E(_1c9.b),_1cc=new T(function(){var _1cd=E(_1c9.c);if(_1cd._==1){var _1ce=E(_1cd.a),_1cf=_1ce.a,_1cg=_1ce.b,_1ch=new T(function(){return B(_1c3(_1c7,_1ca));}),_1ci=function(_1cj){return E(_1ch);},_1ck=new T(function(){var _1cl=new T(function(){var _1cm=new T(function(){return B(A3(_f3,_eT,new T2(1,function(_1cn){return new F(function(){return _fd(0,E(_1cb.a),_1cn);});},new T2(1,function(_1co){return new F(function(){return _fd(0,E(_1cb.b),_1co);});},_6)),_1aY));}),_1cp=B(_vh(_1b4,new T1(0,new T2(1,_ey,_1cm)),_1aR,_1aS,new T1(0,new T(function(){return E(_1cf)-10;})),new T1(0,new T(function(){return E(_1cg)-10;})),_1b5));return new T3(0,_1cp.a,_1cp.b,_1cp.c);});return B(_195(_1aX,_1cl));}),_1cq=B(_195(_1c0,new T(function(){var _1cr=B(_qU(new T1(0,_1cf),new T1(0,_1cg),_1c2));return new T3(0,_1cr.a,_1cr.b,_1cr.c);})));if(!_1cq._){var _1cs=E(_1ck);if(!_1cs._){return E(_1ch);}else{return new T2(1,_1cs.a,new T2(1,_1cs.b,new T1(0,_1ci)));}}else{return new T2(1,_1cq.a,new T2(1,new T2(1,_1cq.b,new T1(0,function(_1ct){return E(_1ck);})),new T1(0,_1ci)));}}else{return B(_1c3(_1c7,_1ca));}},1);_1c4=_1cc;_1c5=_1c9.d;return __continue;}else{return E(_1c7);}})(_1c4,_1c5));if(_1c6!=__continue){return _1c6;}}},_1cu=function(_1cv){var _1cw=E(_1cv);if(!_1cw._){return __Z;}else{var _1cx=E(_1cw.a);return new T2(1,_1cx.a,new T2(1,_1cx.b,new T(function(){return B(_1cu(_1cw.b));})));}},_1cy=function(_1cz){var _1cA=E(_1cz);if(!_1cA._){return __Z;}else{var _1cB=E(_1cA.a);return new T2(1,_1cB.a,new T2(1,_1cB.b,new T(function(){return B(_1cy(_1cA.b));})));}},_1cC=function(_1cD){return new F(function(){return _fd(0,E(_1cD),_6);});},_1cE=function(_1cF,_1cG){var _1cH=E(_1cF);if(!_1cH._){return E(_1af);}else{var _1cI=E(_1cG);if(!_1cI._){return E(_1af);}else{var _1cJ=E(_1cI.a),_1cK=_1cJ.a,_1cL=_1cJ.b,_1cM=new T(function(){return B(_1cE(_1cH.b,_1cI.b));}),_1cN=function(_1cO){var _1cP=E(_1cM);return (_1cP._==0)?new T1(0,new T2(1,_1cO,_1cP.a)):new T2(1,_1cP.a,new T2(1,_1cP.b,new T1(0,function(_1cQ){return new T1(0,new T2(1,_1cO,_1cQ));})));},_1cR=new T(function(){var _1cS=new T(function(){var _1cT=B(_vh(_1b4,new T1(0,new T(function(){return B(_1cC(_1cH.a));})),_1aR,_1aS,new T1(0,new T(function(){return E(_1cK)-10;})),new T1(0,new T(function(){return E(_1cL)-10;})),_1b5));return new T3(0,_1cT.a,_1cT.b,_1cT.c);});return B(_195(_1aX,_1cS));}),_1cU=B(_195(_1aX,new T(function(){var _1cV=B(_qU(new T1(0,_1cK),new T1(0,_1cL),_1c2));return new T3(0,_1cV.a,_1cV.b,_1cV.c);})));if(!_1cU._){var _1cW=E(_1cR);if(!_1cW._){return new F(function(){return _1cN(_1cW.a);});}else{return new T2(1,_1cW.a,new T2(1,_1cW.b,new T1(0,_1cN)));}}else{return new T2(1,_1cU.a,new T2(1,new T2(1,_1cU.b,new T1(0,function(_1cX){return E(_1cR);})),new T1(0,_1cN)));}}}},_1cY=new T(function(){return B(_Y1(0,2147483647));}),_1cZ=function(_1d0){var _1d1=E(_1d0);if(!_1d1._){return __Z;}else{return new F(function(){return _2(B(_1cZ(_1d1.a)),new T2(1,_1d1.b,new T(function(){return B(_1cZ(_1d1.c));})));});}},_1d2=function(_1d3,_1d4){return new F(function(){return A1(_1d3,_1d4);});},_1d5=function(_1aN,_1aO){return new F(function(){return _1d2(_1aN,_1aO);});},_1d6=function(_1d7,_1d8){var _1d9=E(E(_1d7).a)-E(E(_1d8).a);return (_1d9!=0)?(_1d9<=0)? -_1d9<5:_1d9<5:true;},_1da=0.5,_1db=new T1(0,_1da),_1dc=new T4(0,_1a7,_1db,_1aW,_1aW),_1dd=function(_1de){return new F(function(){return _7Z("Voronoi/Main.hs:(44,5)-(46,38)|function flipPt");});},_1df=new T(function(){return B(_1dd(_));}),_1dg=function(_1dh,_1di){var _1dj=E(E(_1dh).a),_1dk=E(E(_1di).a);return (_1dj>=_1dk)?(_1dj!=_1dk)?2:1:0;},_1dl=function(_1dm,_1dn){var _1do=E(E(_1dm).b)-E(E(_1dn).b);return (_1do!=0)?(_1do<=0)? -_1do<5:_1do<5:true;},_1dp=new T4(0,_1a6,_1a6,_s9,_5i),_1dq=new T2(0,_1a6,_1dp),_1dr=new T2(0,_1dq,_6),_1ds=400,_1dt=function(_1du,_1dv,_1dw){var _1dx=new T(function(){return new T1(0,B(_p1(_1dv,_1dw,_oZ)));}),_1dy=function(_1dz){return new T1(1,new T2(1,new T(function(){return B(A1(_1dz,_7));}),new T2(1,_1dx,_6)));};return new F(function(){return A2(_rE,_1du,_1dy);});},_1dA=function(_1dB,_1dC,_1dD,_){var _1dE=__app2(E(_v4),E(_1dC),E(_1dD));return new F(function(){return _qQ(_);});},_1dF=function(_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM){var _1dN=function(_1dO,_1dP,_1dQ,_){var _1dR=function(_1dS,_1dT,_1dU,_){var _1dV=function(_1dW,_1dX,_1dY,_){var _1dZ=function(_1e0,_1e1,_1e2,_){return new F(function(){return _qs(_1dK,function(_1e3,_1e4,_1e5,_){return new F(function(){return _qs(_1dL,_1dA,_1e4,_1e5,_);});},_1e1,_1e2,_);});};return new F(function(){return _qs(_1dJ,_1dZ,_1dX,_1dY,_);});};return new F(function(){return _qs(_1dI,_1dV,_1dT,_1dU,_);});};return new F(function(){return _qs(_1dH,_1dR,_1dP,_1dQ,_);});},_1e6=function(_1e7,_){var _1e8=E(_1e7),_1e9=_1e8.a,_1ea=_1e8.b,_1eb=function(_1ec,_){var _1ed=function(_1ee,_){var _1ef=function(_1eg,_){var _1eh=function(_1ei,_){var _1ej=function(_1ek,_){var _1el=function(_1em){var _1en=new T(function(){return E(_1ee)*E(_1ei)-E(_1ec)*E(_1ek);});return new F(function(){return A1(_1dM,new T2(0,new T(function(){var _1eo=E(_1ee),_1ep=E(_1ek);return ( -(_1eo*E(_1em))+_1eo*E(_1ea)+_1ep*E(_1eg)-_1ep*E(_1e9))/E(_1en);}),new T(function(){var _1eq=E(_1ec),_1er=E(_1ei);return (_1eq*E(_1em)-_1eq*E(_1ea)-_1er*E(_1eg)+_1er*E(_1e9))/E(_1en);})));});};return new F(function(){return _qF(_1dL,_1el,_);});};return new F(function(){return _qF(_1dK,_1ej,_);});};return new F(function(){return _qF(_1dJ,_1eh,_);});};return new F(function(){return _qF(_1dI,_1ef,_);});};return new F(function(){return _qF(_1dH,_1ed,_);});};return new F(function(){return _qF(_1dG,_1eb,_);});};return new T3(0,_1e6,function(_ry,_rz,_){return new F(function(){return _qs(_1dG,_1dN,_ry,_rz,_);});},_7);},_1es=function(_1et,_1eu,_1ev){var _1ew=E(_1eu),_1ex=E(_1ev);switch(_1ex._){case 0:var _1ey=_1ex.a,_1ez=_1ex.b,_1eA=_1ex.c,_1eB=_1ex.d,_1eC=_1ez>>>0;if(((_1et>>>0&((_1eC-1>>>0^4294967295)>>>0^_1eC)>>>0)>>>0&4294967295)==_1ey){return ((_1et>>>0&_1eC)>>>0==0)?new T4(0,_1ey,_1ez,E(B(_1es(_1et,_1ew,_1eA))),E(_1eB)):new T4(0,_1ey,_1ez,E(_1eA),E(B(_1es(_1et,_1ew,_1eB))));}else{var _1eD=(_1et>>>0^_1ey>>>0)>>>0,_1eE=(_1eD|_1eD>>>1)>>>0,_1eF=(_1eE|_1eE>>>2)>>>0,_1eG=(_1eF|_1eF>>>4)>>>0,_1eH=(_1eG|_1eG>>>8)>>>0,_1eI=(_1eH|_1eH>>>16)>>>0,_1eJ=(_1eI^_1eI>>>1)>>>0&4294967295,_1eK=_1eJ>>>0;return ((_1et>>>0&_1eK)>>>0==0)?new T4(0,(_1et>>>0&((_1eK-1>>>0^4294967295)>>>0^_1eK)>>>0)>>>0&4294967295,_1eJ,E(new T2(1,_1et,_1ew)),E(_1ex)):new T4(0,(_1et>>>0&((_1eK-1>>>0^4294967295)>>>0^_1eK)>>>0)>>>0&4294967295,_1eJ,E(_1ex),E(new T2(1,_1et,_1ew)));}break;case 1:var _1eL=_1ex.a;if(_1et!=_1eL){var _1eM=(_1et>>>0^_1eL>>>0)>>>0,_1eN=(_1eM|_1eM>>>1)>>>0,_1eO=(_1eN|_1eN>>>2)>>>0,_1eP=(_1eO|_1eO>>>4)>>>0,_1eQ=(_1eP|_1eP>>>8)>>>0,_1eR=(_1eQ|_1eQ>>>16)>>>0,_1eS=(_1eR^_1eR>>>1)>>>0&4294967295,_1eT=_1eS>>>0;return ((_1et>>>0&_1eT)>>>0==0)?new T4(0,(_1et>>>0&((_1eT-1>>>0^4294967295)>>>0^_1eT)>>>0)>>>0&4294967295,_1eS,E(new T2(1,_1et,_1ew)),E(_1ex)):new T4(0,(_1et>>>0&((_1eT-1>>>0^4294967295)>>>0^_1eT)>>>0)>>>0&4294967295,_1eS,E(_1ex),E(new T2(1,_1et,_1ew)));}else{return new T2(1,_1et,_1ew);}break;default:return new T2(1,_1et,_1ew);}},_1eU=6,_1eV=4,_1eW=0,_1eX=2,_1eY=1,_1eZ=3,_1f0=5,_1f1=new T1(0,_ac),_1f2=function(_1f3,_1f4){return new F(function(){return A1(_1f4,new T2(0,_7,_1f3));});},_1f5=new T1(1,_6),_1f6=0,_1f7=new T4(0,_1f6,_1f6,_s9,_5i),_1f8=new T2(0,_1f6,_1f7),_1f9=new T2(0,_1f8,_6),_1fa=1,_1fb=new T4(0,_1fa,_1fa,_s9,_5i),_1fc=new T2(0,_1fa,_1fb),_1fd=new T2(0,_1fc,_6),_1fe=function(_1ff){return E(E(_1ff).c);},_1fg=new T1(1,_6),_1fh=function(_1fi){var _1fj=function(_){var _1fk=nMV(_1fg);return new T(function(){return B(A1(_1fi,_1fk));});};return new T1(0,_1fj);},_1fl=function(_1fm,_1fn){var _1fo=new T(function(){return B(_1fe(_1fm));}),_1fp=B(_rA(_1fm)),_1fq=function(_1fr){var _1fs=new T(function(){return B(A1(_1fo,new T(function(){return B(A1(_1fn,_1fr));})));});return new F(function(){return A3(_rC,_1fp,_1fs,new T(function(){return B(A2(_aW,_1fp,_1fr));}));});};return new F(function(){return A3(_ak,_1fp,new T(function(){return B(A2(_rE,_1fm,_1fh));}),_1fq);});},_1ft=function(_1fu,_1fv,_1fw,_1fx){var _1fy=new T(function(){return B(A1(_1fu,_1eX));}),_1fz=new T(function(){return B(A1(_1fu,_1eW));}),_1fA=new T(function(){return B(A1(_1fu,_1eV));}),_1fB=new T(function(){return B(_1fl(_4l,_1fx));}),_1fC=new T(function(){return B(A1(_1fu,_1eU));}),_1fD=new T(function(){return B(A1(_1fu,_1f0));}),_1fE=new T(function(){return B(A1(_1fu,_1eZ));}),_1fF=new T(function(){return B(A1(_1fu,_1eY));}),_1fG=function(_1fH){var _1fI=new T(function(){return B(A1(_1fB,_1fH));}),_1fJ=function(_1fK){var _1fL=function(_1fM){var _1fN=E(_1fM),_1fO=_1fN.a,_1fP=_1fN.b,_1fQ=new T(function(){var _1fR=E(_1fy);if(!_1fR._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1fR.a));}}),_1fS=new T(function(){var _1fT=E(_1fz);if(!_1fT._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1fT.a));}}),_1fU=new T(function(){var _1fV=E(_1fA);if(!_1fV._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1fV.a));}}),_1fW=new T(function(){var _1fX=E(_1fC);if(!_1fX._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1fX.a));}}),_1fY=new T(function(){var _1fZ=E(_1fD);if(!_1fZ._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1fZ.a));}}),_1g0=new T(function(){var _1g1=E(_1fE);if(!_1g1._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1g1.a));}}),_1g2=new T(function(){var _1g3=E(_1fF);if(!_1g3._){return E(_1f2);}else{return B(_1dt(_4l,_1fO,_1g3.a));}}),_1g4=function(_){var _1g5=nMV(_1fd),_1g6=_1g5,_1g7=function(_){var _1g8=nMV(_1f9),_1g9=_1g8,_1ga=function(_){var _1gb=nMV(_1f9),_1gc=_1gb,_1gd=function(_){var _1ge=nMV(_1f9),_1gf=_1ge,_1gg=function(_){var _1gh=nMV(_1fd),_1gi=_1gh,_1gj=function(_){var _1gk=nMV(_1f9),_1gl=_1gk,_1gm=function(_1gn,_1go,_1gp,_1gq,_1gr,_1gs){var _1gt=new T(function(){return B(_tf(_1g6,_1gn));}),_1gu=new T(function(){return B(_tf(_1g9,_1go));}),_1gv=new T(function(){return B(_tf(_1gc,_1gp));}),_1gw=new T(function(){return B(_tf(_1gf,_1gq));}),_1gx=new T(function(){return B(_tf(_1gi,_1gr));}),_1gy=new T(function(){return B(_tf(_1gl,_1gs));}),_1gz=function(_1gA){var _1gB=new T(function(){return B(A1(_1gt,_1gA));}),_1gC=function(_1gD){var _1gE=function(_1gF){return new F(function(){return A1(_1gD,new T2(0,_7,E(_1gF).b));});},_1gG=function(_1gH){return new F(function(){return A2(_1gy,E(_1gH).b,_1gE);});},_1gI=function(_1gJ){return new F(function(){return A2(_1gx,E(_1gJ).b,_1gG);});},_1gK=function(_1gL){return new F(function(){return A2(_1gw,E(_1gL).b,_1gI);});},_1gM=function(_1gN){return new F(function(){return A2(_1gv,E(_1gN).b,_1gK);});};return new F(function(){return A1(_1gB,function(_1gO){return new F(function(){return A2(_1gu,E(_1gO).b,_1gM);});});});};return E(_1gC);};return E(_1gz);},_1gP=new T2(1,new T2(2,_1gm,_7),_1f1),_1gQ=new T(function(){var _1gR=E(_1fw);if(!_1gR._){return E(_1gP);}else{return new T2(1,_1gR.a,new T2(1,_1gR.b,new T1(0,function(_1gS){return E(_1gP);})));}}),_1gT=new T(function(){var _1gU=B(_1dF(new T2(2,new T3(0,_te,_1d2,_1g6),_2E),new T2(2,new T3(0,_te,_1d2,_1g9),_2E),new T2(2,new T3(0,_te,_1d2,_1gc),_2E),new T2(2,new T3(0,_te,_1d2,_1gf),_2E),new T2(2,new T3(0,_te,_1d2,_1gi),_2E),new T2(2,new T3(0,_te,_1d2,_1gl),_2E),E(_1fv).a));return new T3(0,_1gU.a,_1gU.b,_1gU.c);}),_1gV=function(_){var _1gW=nMV(_1f5),_1gX=_1gW,_1gY=new T(function(){var _1gZ=function(_1h0){return new F(function(){return _1h1(E(_1h0).b);});},_1h2=function(_1h3){var _1h4=new T(function(){return B(A2(_1g2,_1h3,_1h5));}),_1h6=new T(function(){return B(A2(_1fQ,_1h3,_1gZ));}),_1h7=new T(function(){return B(A2(_1g0,_1h3,_1h8));}),_1h9=new T(function(){return B(_1h2(_1h3));}),_1ha=function(_1hb){var _1hc=E(_1hb);if(!_1hc._){return (!E(_1hc.a))?E(_1h9):E(_1h7);}else{var _1hd=function(_){var _1he=B(A2(E(_1gT).a,_1hc.a,_));return new T(function(){if(!E(_1he)){return E(_1h6);}else{return E(_1h4);}});};return new T1(0,_1hd);}};return new T1(0,B(_pd(_1gX,_1ha)));},_1h5=function(_1hf){return new F(function(){return _1h2(E(_1hf).b);});},_1h1=function(_1hg){var _1hh=new T(function(){return B(_1h1(_1hg));}),_1hi=new T(function(){return B(A2(_1fS,_1hg,_1h5));}),_1hj=function(_1hk){var _1hl=E(_1hk);if(!_1hl._){return E(_1hh);}else{var _1hm=function(_){var _1hn=B(A2(E(_1gT).a,_1hl.a,_));return new T(function(){if(!E(_1hn)){return E(_1hh);}else{return E(_1hi);}});};return new T1(0,_1hm);}};return new T1(0,B(_pd(_1gX,_1hj)));},_1ho=function(_1hp){var _1hq=new T(function(){return B(A2(_1fU,_1hp,_1h8));}),_1hr=new T(function(){return B(A2(_1fQ,_1hp,_1hs));}),_1ht=new T(function(){return B(_1ho(_1hp));}),_1hu=new T(function(){return B(A2(_1fY,_1hp,_1h5));}),_1hv=function(_1hw){var _1hx=E(_1hw);if(!_1hx._){return (!E(_1hx.a))?E(_1hu):E(_1ht);}else{var _1hy=function(_){var _1hz=B(A2(E(_1gT).a,_1hx.a,_));return new T(function(){if(!E(_1hz)){return E(_1hr);}else{return E(_1hq);}});};return new T1(0,_1hy);}};return new T1(0,B(_pd(_1gX,_1hv)));},_1h8=function(_1hA){return new F(function(){return _1ho(E(_1hA).b);});},_1hB=function(_1hC){var _1hD=new T(function(){return B(A2(_1fS,_1hC,_1h8));}),_1hE=new T(function(){return B(A2(_1fU,_1hC,_1hs));}),_1hF=new T(function(){return B(_1hB(_1hC));}),_1hG=new T(function(){return B(A2(_1fW,_1hC,_1gZ));}),_1hH=function(_1hI){var _1hJ=E(_1hI);if(!_1hJ._){return (!E(_1hJ.a))?E(_1hG):E(_1hF);}else{var _1hK=function(_){var _1hL=B(A2(E(_1gT).a,_1hJ.a,_));return new T(function(){if(!E(_1hL)){return E(_1hE);}else{return E(_1hD);}});};return new T1(0,_1hK);}};return new T1(0,B(_pd(_1gX,_1hH)));},_1hs=function(_1hM){return new F(function(){return _1hB(E(_1hM).b);});};return B(_1h1(_1fP));}),_1hN=new T(function(){var _1hO=function(_1hP){var _1hQ=E(_1hP);return new F(function(){return A1(_1fK,new T2(0,new T(function(){return new T3(0,E(_1hQ.a),_1gQ,E(_1fO));}),_1hQ.b));});},_1hR=function(_1hS,_1hT,_1hU){var _1hV=new T(function(){return E(E(_1hS).d);}),_1hW=new T(function(){return E(E(_1hV).a);}),_1hX=new T(function(){var _1hY=E(_1hS);return new T4(0,E(_1hY.a),_1hY.b,E(_1hY.c),E(new T2(0,new T(function(){return E(_1hW)+1|0;}),new T(function(){return B(_1es(E(_1hW),_1gX,E(_1hV).b));}))));});return new F(function(){return A1(_1hU,new T2(0,new T2(0,_1hW,_1hX),_1hT));});};return B(A(_rN,[_4l,_1fP,_1hR,_1fP,_1hO]));});return new T1(1,new T2(1,_1hN,new T2(1,_1gY,_6)));};return new T1(0,_1gV);};return new T1(0,_1gj);};return new T1(0,_1gg);};return new T1(0,_1gd);};return new T1(0,_1ga);};return new T1(0,_1g7);};return new T1(0,_1g4);};return new F(function(){return A1(_1fI,_1fL);});};return E(_1fJ);};return E(_1fG);},_1hZ=function(_1i0,_1i1,_1i2){while(1){var _1i3=E(_1i2);if(!_1i3._){return false;}else{if(!B(A2(_1i0,_1i3.a,_1i1))){_1i2=_1i3.b;continue;}else{return true;}}}},_1i4=function(_1i5,_1i6){var _1i7=function(_1i8,_1i9){while(1){var _1ia=B((function(_1ib,_1ic){var _1id=E(_1ib);if(!_1id._){return __Z;}else{var _1ie=_1id.a,_1if=_1id.b;if(!B(_1hZ(_1i5,_1ie,_1ic))){return new T2(1,_1ie,new T(function(){return B(_1i7(_1if,new T2(1,_1ie,_1ic)));}));}else{var _1ig=_1ic;_1i8=_1if;_1i9=_1ig;return __continue;}}})(_1i8,_1i9));if(_1ia!=__continue){return _1ia;}}};return new F(function(){return _1i7(_1i6,_6);});},_1ih=function(_1ii){return E(E(_1ii).a);},_1ij=function(_1ik){return E(E(_1ik).a);},_1il=function(_1im,_1in,_1io){var _1ip=E(_1in),_1iq=E(_1io),_1ir=new T(function(){var _1is=B(_1ih(_1im)),_1it=B(_1il(_1im,_1iq,B(A3(_nO,_1is,new T(function(){return B(A3(_1ij,_1is,_1iq,_1iq));}),_1ip))));return new T2(1,_1it.a,_1it.b);});return new T2(0,_1ip,_1ir);},_1iu=function(_1iv){return E(E(_1iv).b);},_1iw=function(_1ix,_1iy){var _1iz=E(_1iy);if(!_1iz._){return __Z;}else{var _1iA=_1iz.a;return (!B(A1(_1ix,_1iA)))?__Z:new T2(1,_1iA,new T(function(){return B(_1iw(_1ix,_1iz.b));}));}},_1iB=function(_1iC,_1iD,_1iE,_1iF,_1iG){var _1iH=B(_1il(_1iD,_1iE,_1iF)),_1iI=new T(function(){var _1iJ=new T(function(){return B(_1ih(_1iD));}),_1iK=new T(function(){return B(A3(_1iu,_1iD,new T(function(){return B(A3(_nO,_1iJ,_1iF,_1iE));}),new T(function(){return B(A2(_cW,_1iJ,_jx));})));});if(!B(A3(_zB,_1iC,_1iF,_1iE))){var _1iL=new T(function(){return B(A3(_1ij,_1iJ,_1iG,_1iK));});return function(_1iM){return new F(function(){return A3(_zB,_1iC,_1iM,_1iL);});};}else{var _1iN=new T(function(){return B(A3(_1ij,_1iJ,_1iG,_1iK));});return function(_1iO){return new F(function(){return A3(_zz,_1iC,_1iO,_1iN);});};}});return new F(function(){return _1iw(_1iI,new T2(1,_1iH.a,_1iH.b));});},_1iP=function(_1iQ,_){var _1iR=E(_1iQ);if(!_1iR._){return _6;}else{var _1iS=B(A1(_1iR.a,_)),_1iT=B(_1iP(_1iR.b,_));return new T2(1,_1iS,_1iT);}},_1iU=function(_1iV,_1iW){while(1){var _1iX=E(_1iV);if(!_1iX._){return E(_1iW);}else{var _1iY=new T2(1,_1iX.a,_1iW);_1iV=_1iX.b;_1iW=_1iY;continue;}}},_1iZ=function(_1j0){var _1j1=E(_1j0);return (_1j1._==0)?E(_Yc):E(_1j1.b);},_1j2=function(_1j3,_1j4){return function(_){var _1j5=B(_146(_)),_1j6=new T(function(){return E(E(_1j5).b);}),_1j7=new T(function(){return E(_1j6)+100;}),_1j8=new T(function(){return E(E(_1j5).a)/2;}),_1j9=new T(function(){return E(_1j8)/2;}),_1ja=new T(function(){return E(_1j8)/5+30;}),_1jb=new T(function(){return E(_1j8)/5;}),_1jc=function(_){var _1jd=function(_){var _1je=B(_oB(new T2(0,_1a6,_1j8),_)),_1jf=B(_oB(new T2(0,_1a6,_1j6),_));return new T2(0,_1je,_1jf);},_1jg=function(_1jh){var _1ji=E(_1jh);return (_1ji==1)?E(new T2(1,_1jd,_6)):new T2(1,_1jd,new T(function(){return B(_1jg(_1ji-1|0));}));},_1jj=B(_1iP(B(_1jg(100)),_)),_1jk=new T(function(){var _1jl=B(_Y7(_Yd,B(_Yg(_1dg,B(_tC(B(_1i4(_1d6,B(_1i4(_1dl,_1jj)))),10))))));if(!_1jl._){return E(_1df);}else{var _1jm=E(_1jl.a),_1jn=E(_1jl.b);if(!_1jn._){return E(_1df);}else{var _1jo=E(_1jn.a),_1jp=E(_1jm.a),_1jq=E(_1jo.a);if(_1jp<=_1jq){return E(_1jl);}else{return new T2(1,new T2(0,_1jq,_1jm.b),new T2(1,new T2(0,_1jp,_1jo.b),_1jn.b));}}}}),_1jr=new T(function(){var _1js=B(_Z5(_1jk,_1j8,_1j6));return new T2(0,_1js.a,_1js.b);}),_1jt=new T(function(){return E(E(_1jr).b);}),_1ju=new T(function(){return E(B(_oU(_1jk,0)).a)>E(B(_oU(_1jk,1)).a);}),_1jv=function(_1jw){var _1jx=E(_1jw);if(!_1jx._){return E(_oI);}else{var _1jy=E(_1jx.a),_1jz=B(_uZ(_1jy,_1jt));if(!_1jz._){return E(_oI);}else{var _1jA=new T(function(){return E(E(_1jz.a).b);}),_1jB=new T(function(){return E(E(_1jA).c);}),_1jC=new T(function(){var _1jD=B(_uF(_1j9,_1ja,_ch,_1jb,_1jB)),_1jE=function(_1jF){var _1jG=E(_1jF);if(!_1jG._){return E(_oI);}else{var _1jH=E(_1jG.a),_1jI=_1jH.a,_1jJ=_1jH.c,_1jK=_1jH.d,_1jL=E(_1jH.b),_1jM=new T(function(){return E(E(_1jI).b);}),_1jN=new T(function(){return E(E(_1jI).a)+E(_1j8);}),_1jO=new T(function(){return B(_1jE(_1jG.b));}),_1jP=function(_1jQ){return E(_1jO);},_1jR=new T(function(){var _1jS=new T(function(){var _1jT=new T(function(){var _1jU=function(_1jV){var _1jW=E(_1jJ);if(!_1jW._){return new T3(0,_5k,_5f,_7);}else{var _1jX=E(_1jW.c);if(!_1jX._){return new T3(0,_5k,_5f,_7);}else{var _1jY=new T(function(){var _1jZ=E(_1jD);if(!_1jZ._){return E(_1ai);}else{var _1k0=_1jZ.b,_1k1=E(_1jZ.a),_1k2=E(_1k1.b),_1k3=E(_1jX.b),_1k4=E(_1k3.a).a,_1k5=E(_1k3.b).a;if(E(_1k2.a)!=_1k4){var _1k6=function(_1k7){while(1){var _1k8=E(_1k7);if(!_1k8._){return E(_1ai);}else{var _1k9=_1k8.b,_1ka=E(_1k8.a),_1kb=E(_1ka.b);if(E(_1kb.a)!=_1k4){_1k7=_1k9;continue;}else{if(E(_1kb.b)!=_1k5){_1k7=_1k9;continue;}else{return new T5(0,_1ka.a,_1kb,_1ka.c,_1ka.d,_1ka.e);}}}}};return E(B(_1k6(_1k0)).a);}else{if(E(_1k2.b)!=_1k5){var _1kc=function(_1kd){while(1){var _1ke=E(_1kd);if(!_1ke._){return E(_1ai);}else{var _1kf=_1ke.b,_1kg=E(_1ke.a),_1kh=E(_1kg.b);if(E(_1kh.a)!=_1k4){_1kd=_1kf;continue;}else{if(E(_1kh.b)!=_1k5){_1kd=_1kf;continue;}else{return new T5(0,_1kg.a,_1kh,_1kg.c,_1kg.d,_1kg.e);}}}}};return E(B(_1kc(_1k0)).a);}else{return E(_1k1.a);}}}}),_1ki=new T(function(){return E(E(_1jY).b);}),_1kj=new T(function(){return E(E(_1jY).a)+E(_1j8);}),_1kk=new T(function(){return Math.sqrt(Math.pow(E(_1kj)-E(_1jN),2)+Math.pow(E(_1ki)-E(_1jM),2));}),_1kl=new T(function(){return (E(_1kj)-E(_1jN))/E(_1kk);}),_1km=new T(function(){return (E(_1ki)-E(_1jM))/E(_1kk);});return new F(function(){return _um(new T2(0,new T1(0,new T(function(){return E(_1jN)+E(_1kl)*E(_1jK);})),new T1(0,new T(function(){return E(_1jM)+E(_1km)*E(_1jK);}))),new T2(0,new T1(0,new T(function(){return E(_1kj)-E(_1kl)*E(_1jK)/2;})),new T1(0,new T(function(){return E(_1ki)-E(_1km)*E(_1jK)/2;}))));});}}},_1kn=E(_1jJ);if(!_1kn._){var _1ko=new T(function(){var _1kp=B(_1jU(_));return new T3(0,_1kp.a,_1kp.b,_1kp.c);});return new T3(0,function(_1kq,_){var _1kr=B(A2(E(_1ko).a,_1kq,_));return _5i;},function(_1ks,_1kt,_){return new F(function(){return A3(E(_1ko).b,_1ks,_1kt,_);});},new T(function(){return E(E(_1ko).c);}));}else{var _1ku=E(_1kn.a);if(!_1ku._){var _1kv=new T(function(){var _1kw=B(_1jU(_));return new T3(0,_1kw.a,_1kw.b,_1kw.c);});return new T3(0,function(_1kx,_){var _1ky=B(A2(E(_1kv).a,_1kx,_));return _5i;},function(_1kz,_1kA,_){return new F(function(){return A3(E(_1kv).b,_1kz,_1kA,_);});},new T(function(){return E(E(_1kv).c);}));}else{var _1kB=new T(function(){var _1kC=E(_1jD);if(!_1kC._){return E(_1ai);}else{var _1kD=_1kC.b,_1kE=E(_1kC.a),_1kF=E(_1kE.b),_1kG=E(_1ku.b),_1kH=E(_1kG.a).a,_1kI=E(_1kG.b).a;if(E(_1kF.a)!=_1kH){var _1kJ=function(_1kK){while(1){var _1kL=E(_1kK);if(!_1kL._){return E(_1ai);}else{var _1kM=_1kL.b,_1kN=E(_1kL.a),_1kO=E(_1kN.b);if(E(_1kO.a)!=_1kH){_1kK=_1kM;continue;}else{if(E(_1kO.b)!=_1kI){_1kK=_1kM;continue;}else{return new T5(0,_1kN.a,_1kO,_1kN.c,_1kN.d,_1kN.e);}}}}};return E(B(_1kJ(_1kD)).a);}else{if(E(_1kF.b)!=_1kI){var _1kP=function(_1kQ){while(1){var _1kR=E(_1kQ);if(!_1kR._){return E(_1ai);}else{var _1kS=_1kR.b,_1kT=E(_1kR.a),_1kU=E(_1kT.b);if(E(_1kU.a)!=_1kH){_1kQ=_1kS;continue;}else{if(E(_1kU.b)!=_1kI){_1kQ=_1kS;continue;}else{return new T5(0,_1kT.a,_1kU,_1kT.c,_1kT.d,_1kT.e);}}}}};return E(B(_1kP(_1kD)).a);}else{return E(_1kE.a);}}}}),_1kV=new T(function(){return E(E(_1kB).b);}),_1kW=new T(function(){return E(E(_1kB).a)+E(_1j8);}),_1kX=new T(function(){return Math.sqrt(Math.pow(E(_1kW)-E(_1jN),2)+Math.pow(E(_1kV)-E(_1jM),2));}),_1kY=new T(function(){return (E(_1kW)-E(_1jN))/E(_1kX);}),_1kZ=new T(function(){return (E(_1kV)-E(_1jM))/E(_1kX);}),_1l0=B(_um(new T2(0,new T1(0,new T(function(){return E(_1jN)+E(_1kY)*E(_1jK);})),new T1(0,new T(function(){return E(_1jM)+E(_1kZ)*E(_1jK);}))),new T2(0,new T1(0,new T(function(){return E(_1kW)-E(_1kY)*E(_1jK)/2;})),new T1(0,new T(function(){return E(_1kV)-E(_1kZ)*E(_1jK)/2;}))))),_1l1=new T(function(){var _1l2=B(_1jU(_));return new T3(0,_1l2.a,_1l2.b,_1l2.c);}),_1l3=function(_1l4,_){var _1l5=B(A2(_1l0.a,_1l4,_)),_1l6=B(A2(E(_1l1).a,_1l4,_));return new T(function(){return B(_13X(_1l5,_1l6));});};return new T3(0,_1l3,function(_1l7,_1l8,_){var _1l9=B(A3(_1l0.b,_1l7,_1l8,_));return new F(function(){return A3(E(_1l1).b,_1l7,_1l8,_);});},new T(function(){return E(E(_1l1).c);}));}}});return B(_1bk(_1b0,_1aX,_1jT));}),_1la=new T(function(){var _1lb=E(_1jK),_1lc=_1lb/2,_1ld=new T(function(){return B(A3(_f3,_eT,new T2(1,function(_1le){return new F(function(){return _fd(0,E(_1jL.a),_1le);});},new T2(1,function(_1lf){return new F(function(){return _fd(0,E(_1jL.b),_1lf);});},_6)),_1aY));});if(_1lc<=10){var _1lg=B(_vh(_1b4,new T1(0,new T2(1,_ey,_1ld)),_140,_143,new T1(0,new T(function(){if(!E(_1jH.e)){return E(_1jN)-(_1lb+15);}else{return E(_1jN)+_1lb+15;}})),new T1(0,_1jM),new T1(0,new T(function(){if(_1lc>10){return _1lc;}else{return E(_1ae);}}))));return new T3(0,_1lg.a,_1lg.b,_1lg.c);}else{var _1lh=B(_vh(_1b4,new T1(0,new T2(1,_ey,_1ld)),_140,_143,new T1(0,_1jN),new T1(0,_1jM),new T1(0,new T(function(){if(_1lc>10){return _1lc;}else{return E(_1ae);}}))));return new T3(0,_1lh.a,_1lh.b,_1lh.c);}}),_1li=B(_195(_1aX,_1la));if(!_1li._){return E(_1jS);}else{return new T2(1,_1li.a,new T2(1,_1li.b,new T1(0,function(_1lj){return E(_1jS);})));}}),_1lk=B(_1bk(_1b0,_1aX,new T(function(){var _1ll=B(_qU(new T1(0,_1jN),new T1(0,_1jM),new T1(0,_1jK)));return new T3(0,_1ll.a,_1ll.b,_1ll.c);})));if(!_1lk._){var _1lm=E(_1jR);return (_1lm._==0)?E(_1jO):new T2(1,_1lm.a,new T2(1,_1lm.b,new T1(0,_1jP)));}else{return new T2(1,_1lk.a,new T2(1,new T2(1,_1lk.b,new T1(0,function(_1ln){return E(_1jR);})),new T1(0,_1jP)));}}};return B(_1jE(_1jD));}),_1lo=new T(function(){var _1lp=E(_1jA),_1lq=new T(function(){var _1lr=new T(function(){var _1ls=new T(function(){var _1lt=new T(function(){var _1lu=B(_1cZ(_1jB));if(B(_tM(_1lu,0))==2){if(!E(_1ju)){return B(_1cu(_1lu));}else{return B(_1cy(B(_1iU(_1lu,_6))));}}else{return B(_1bW(_1lu));}}),_1lv=new T(function(){var _1lw=E(_1lt);if(!_1lw._){return E(_1ai);}else{return E(_1lw.a);}}),_1lx=new T(function(){return B(_1aE(B(_1iZ(_1lt))));}),_1ly=new T2(1,_1lv,_1lx),_1lz=new T(function(){return B(_tM(_1ly,0))-1|0;}),_1lA=function(_1lB,_1lC){var _1lD=E(_1lB);if(!_1lD._){return E(_1af);}else{var _1lE=E(_1lC);if(!_1lE._){return E(_1af);}else{var _1lF=E(_1lE.a),_1lG=_1lF.b,_1lH=_1lF.c,_1lI=new T(function(){return B(_1lA(_1lD.b,_1lE.b));}),_1lJ=function(_1lK){var _1lL=E(_1lI);return (_1lL._==0)?new T1(0,new T2(1,_1lK,_1lL.a)):new T2(1,_1lL.a,new T2(1,_1lL.b,new T1(0,function(_1lM){return new T1(0,new T2(1,_1lK,_1lM));})));};if(_1lH>_1jy){return new F(function(){return _1lJ(_7);});}else{var _1lN=E(_1lD.a),_1lO=function(_1lP,_1lQ){var _1lR=E(_1lz),_1lS=function(_1lT,_1lU){var _1lV=new T(function(){return _1lT<=_1lP;}),_1lW=function(_1lX){var _1lY=function(_1lZ){var _1m0=E(_1lZ);if(!_1m0._){return E(_oI);}else{var _1m1=E(_1m0.a),_1m2=new T(function(){return B(_1lY(_1m0.b));}),_1m3=function(_1m4){return E(_1m2);},_1m5=function(_1m6,_1m7){var _1m8=(_1lG*_1lG-(_1lG+_1lG)*_1m6+_1lH*_1lH-_1jy*_1jy+_1m6*_1m6)/(_1lH+_1lH-(_1jy+_1jy));if(_1m8<0){return E(_oI);}else{if(_1m8>E(_1j6)){return E(_oI);}else{var _1m9=new T(function(){var _1ma=_1m1+_1lX,_1mb=new T(function(){if(_1ma>_1lT){if(!E(_1lV)){return E(_1lU);}else{return E(_1lQ);}}else{if(_1ma>_1lP){return _1ma;}else{return E(_1lQ);}}}),_1mc=B(_um(new T2(0,new T1(0,_1m7),new T1(0,_1m8)),new T2(0,new T1(0,_1mb),new T1(0,new T(function(){var _1md=E(_1mb);return (_1lG*_1lG-(_1lG+_1lG)*_1md+_1lH*_1lH-_1jy*_1jy+_1md*_1md)/(_1lH+_1lH-(_1jy+_1jy));})))));return new T3(0,_1mc.a,_1mc.b,_1mc.c);});return new F(function(){return _1bk(_1b0,_1dc,_1m9);});}}};if(_1m1>_1lT){if(!E(_1lV)){var _1me=B(_1m5(_1lT,_1lU));return (_1me._==0)?E(_1m2):new T2(1,_1me.a,new T2(1,_1me.b,new T1(0,_1m3)));}else{var _1mf=B(_1m5(_1lP,_1lQ));return (_1mf._==0)?E(_1m2):new T2(1,_1mf.a,new T2(1,_1mf.b,new T1(0,_1m3)));}}else{if(_1m1>_1lP){var _1mg=B(_1m5(_1m1,_1m1));return (_1mg._==0)?E(_1m2):new T2(1,_1mg.a,new T2(1,_1mg.b,new T1(0,_1m3)));}else{var _1mh=B(_1m5(_1lP,_1lQ));return (_1mh._==0)?E(_1m2):new T2(1,_1mh.a,new T2(1,_1mh.b,new T1(0,_1m3)));}}}},_1mi=B(_1lY(B(_1iB(_bK,_a3,_1lQ,_1lP+_1lX,_1lU))));if(!_1mi._){return new F(function(){return _1lJ(_1mi.a);});}else{return new T2(1,_1mi.a,new T2(1,_1mi.b,new T1(0,_1lJ)));}};if((_1lT-_1lP)/15<=20){return new F(function(){return _1lW((_1lT-_1lP)/15);});}else{return new F(function(){return _1lW((_1lT-_1lP)/50);});}};if(_1lN>=_1lR){var _1mj=E(_1j8);return new F(function(){return _1lS(_1mj,_1mj);});}else{if(_1lN>=_1lR){return E(_1aQ);}else{var _1mk=B(_oU(_1ly,_1lN+1|0)),_1ml=_1mk.b,_1mm=_1mk.c,_1mn=_1lH-_1mm;if(_1mn!=0){if(_1mn<=0){if( -_1mn>=1.0e-7){var _1mo=(_1lH*_1ml+Math.sqrt(((_1lG-_1ml)*(_1lG-_1ml)+_1mn*_1mn)*(_1lH-_1jy)*(_1mm-_1jy))+(_1lG*(_1jy-_1mm)-_1ml*_1jy))/_1mn;return new F(function(){return _1lS(_1mo,_1mo);});}else{var _1mp=(_1lG+_1ml)/2;return new F(function(){return _1lS(_1mp,_1mp);});}}else{if(_1mn>=1.0e-7){var _1mq=(_1lH*_1ml+Math.sqrt(((_1lG-_1ml)*(_1lG-_1ml)+_1mn*_1mn)*(_1lH-_1jy)*(_1mm-_1jy))+(_1lG*(_1jy-_1mm)-_1ml*_1jy))/_1mn;return new F(function(){return _1lS(_1mq,_1mq);});}else{var _1mr=(_1lG+_1ml)/2;return new F(function(){return _1lS(_1mr,_1mr);});}}}else{var _1ms=(_1lG+_1ml)/2;return new F(function(){return _1lS(_1ms,_1ms);});}}}};if(_1lN<=0){return new F(function(){return _1lO(0,0);});}else{var _1mt=B(_oU(_1ly,_1lN-1|0)),_1mu=_1mt.b,_1mv=_1mt.c,_1mw=_1mv-_1lH;if(_1mw!=0){if(_1mw<=0){if( -_1mw>=1.0e-7){var _1mx=(_1mv*_1lG+Math.sqrt(((_1mu-_1lG)*(_1mu-_1lG)+_1mw*_1mw)*(_1mv-_1jy)*(_1lH-_1jy))+(_1mu*(_1jy-_1lH)-_1lG*_1jy))/_1mw;return new F(function(){return _1lO(_1mx,_1mx);});}else{var _1my=(_1mu+_1lG)/2;return new F(function(){return _1lO(_1my,_1my);});}}else{if(_1mw>=1.0e-7){var _1mz=(_1mv*_1lG+Math.sqrt(((_1mu-_1lG)*(_1mu-_1lG)+_1mw*_1mw)*(_1mv-_1jy)*(_1lH-_1jy))+(_1mu*(_1jy-_1lH)-_1lG*_1jy))/_1mw;return new F(function(){return _1lO(_1mz,_1mz);});}else{var _1mA=(_1mu+_1lG)/2;return new F(function(){return _1lO(_1mA,_1mA);});}}}else{var _1mB=(_1mu+_1lG)/2;return new F(function(){return _1lO(_1mB,_1mB);});}}}}}},_1mC=function(_1mD,_1mE,_1mF){var _1mG=E(_1mD);if(!_1mG._){return E(_1af);}else{var _1mH=E(_1mE),_1mI=_1mH.b,_1mJ=_1mH.c,_1mK=new T(function(){return B(_1lA(_1mG.b,_1mF));}),_1mL=function(_1mM){var _1mN=E(_1mK);return (_1mN._==0)?new T1(0,new T2(1,_1mM,_1mN.a)):new T2(1,_1mN.a,new T2(1,_1mN.b,new T1(0,function(_1mO){return new T1(0,new T2(1,_1mM,_1mO));})));};if(_1mJ>_1jy){return new F(function(){return _1mL(_7);});}else{var _1mP=E(_1mG.a),_1mQ=function(_1mR,_1mS){var _1mT=E(_1lz),_1mU=function(_1mV,_1mW){var _1mX=new T(function(){return _1mV<=_1mR;}),_1mY=function(_1mZ){var _1n0=function(_1n1){var _1n2=E(_1n1);if(!_1n2._){return E(_oI);}else{var _1n3=E(_1n2.a),_1n4=new T(function(){return B(_1n0(_1n2.b));}),_1n5=function(_1n6){return E(_1n4);},_1n7=function(_1n8,_1n9){var _1na=(_1mI*_1mI-(_1mI+_1mI)*_1n8+_1mJ*_1mJ-_1jy*_1jy+_1n8*_1n8)/(_1mJ+_1mJ-(_1jy+_1jy));if(_1na<0){return E(_oI);}else{if(_1na>E(_1j6)){return E(_oI);}else{var _1nb=new T(function(){var _1nc=_1n3+_1mZ,_1nd=new T(function(){if(_1nc>_1mV){if(!E(_1mX)){return E(_1mW);}else{return E(_1mS);}}else{if(_1nc>_1mR){return _1nc;}else{return E(_1mS);}}}),_1ne=B(_um(new T2(0,new T1(0,_1n9),new T1(0,_1na)),new T2(0,new T1(0,_1nd),new T1(0,new T(function(){var _1nf=E(_1nd);return (_1mI*_1mI-(_1mI+_1mI)*_1nf+_1mJ*_1mJ-_1jy*_1jy+_1nf*_1nf)/(_1mJ+_1mJ-(_1jy+_1jy));})))));return new T3(0,_1ne.a,_1ne.b,_1ne.c);});return new F(function(){return _1bk(_1b0,_1dc,_1nb);});}}};if(_1n3>_1mV){if(!E(_1mX)){var _1ng=B(_1n7(_1mV,_1mW));return (_1ng._==0)?E(_1n4):new T2(1,_1ng.a,new T2(1,_1ng.b,new T1(0,_1n5)));}else{var _1nh=B(_1n7(_1mR,_1mS));return (_1nh._==0)?E(_1n4):new T2(1,_1nh.a,new T2(1,_1nh.b,new T1(0,_1n5)));}}else{if(_1n3>_1mR){var _1ni=B(_1n7(_1n3,_1n3));return (_1ni._==0)?E(_1n4):new T2(1,_1ni.a,new T2(1,_1ni.b,new T1(0,_1n5)));}else{var _1nj=B(_1n7(_1mR,_1mS));return (_1nj._==0)?E(_1n4):new T2(1,_1nj.a,new T2(1,_1nj.b,new T1(0,_1n5)));}}}},_1nk=B(_1n0(B(_1iB(_bK,_a3,_1mS,_1mR+_1mZ,_1mW))));if(!_1nk._){return new F(function(){return _1mL(_1nk.a);});}else{return new T2(1,_1nk.a,new T2(1,_1nk.b,new T1(0,_1mL)));}};if((_1mV-_1mR)/15<=20){return new F(function(){return _1mY((_1mV-_1mR)/15);});}else{return new F(function(){return _1mY((_1mV-_1mR)/50);});}};if(_1mP>=_1mT){var _1nl=E(_1j8);return new F(function(){return _1mU(_1nl,_1nl);});}else{if(_1mP>=_1mT){return E(_1aQ);}else{var _1nm=B(_oU(_1ly,_1mP+1|0)),_1nn=_1nm.b,_1no=_1nm.c,_1np=_1mJ-_1no;if(_1np!=0){if(_1np<=0){if( -_1np>=1.0e-7){var _1nq=(_1mJ*_1nn+Math.sqrt(((_1mI-_1nn)*(_1mI-_1nn)+_1np*_1np)*(_1mJ-_1jy)*(_1no-_1jy))+(_1mI*(_1jy-_1no)-_1nn*_1jy))/_1np;return new F(function(){return _1mU(_1nq,_1nq);});}else{var _1nr=(_1mI+_1nn)/2;return new F(function(){return _1mU(_1nr,_1nr);});}}else{if(_1np>=1.0e-7){var _1ns=(_1mJ*_1nn+Math.sqrt(((_1mI-_1nn)*(_1mI-_1nn)+_1np*_1np)*(_1mJ-_1jy)*(_1no-_1jy))+(_1mI*(_1jy-_1no)-_1nn*_1jy))/_1np;return new F(function(){return _1mU(_1ns,_1ns);});}else{var _1nt=(_1mI+_1nn)/2;return new F(function(){return _1mU(_1nt,_1nt);});}}}else{var _1nu=(_1mI+_1nn)/2;return new F(function(){return _1mU(_1nu,_1nu);});}}}};if(_1mP<=0){return new F(function(){return _1mQ(0,0);});}else{var _1nv=B(_oU(_1ly,_1mP-1|0)),_1nw=_1nv.b,_1nx=_1nv.c,_1ny=_1nx-_1mJ;if(_1ny!=0){if(_1ny<=0){if( -_1ny>=1.0e-7){var _1nz=(_1nx*_1mI+Math.sqrt(((_1nw-_1mI)*(_1nw-_1mI)+_1ny*_1ny)*(_1nx-_1jy)*(_1mJ-_1jy))+(_1nw*(_1jy-_1mJ)-_1mI*_1jy))/_1ny;return new F(function(){return _1mQ(_1nz,_1nz);});}else{var _1nA=(_1nw+_1mI)/2;return new F(function(){return _1mQ(_1nA,_1nA);});}}else{if(_1ny>=1.0e-7){var _1nB=(_1nx*_1mI+Math.sqrt(((_1nw-_1mI)*(_1nw-_1mI)+_1ny*_1ny)*(_1nx-_1jy)*(_1mJ-_1jy))+(_1nw*(_1jy-_1mJ)-_1mI*_1jy))/_1ny;return new F(function(){return _1mQ(_1nB,_1nB);});}else{var _1nC=(_1nw+_1mI)/2;return new F(function(){return _1mQ(_1nC,_1nC);});}}}else{var _1nD=(_1nw+_1mI)/2;return new F(function(){return _1mQ(_1nD,_1nD);});}}}}};return B(_1mC(_1cY,_1lv,_1lx));});return B(_aT(_7,_1ls));});if(!E(_1lp.a)){return E(_1lr);}else{var _1nE=E(_1lp.d),_1nF=B(_oU(_1jk,E(_1nE.a))),_1nG=B(_oU(_1jk,E(_1nE.b))),_1nH=B(_oU(_1jk,E(_1nE.c))),_1nI=E(_1nF.a),_1nJ=E(_1nF.b),_1nK=E(_1nH.a)-_1nI,_1nL=E(_1nH.b)-_1nJ,_1nM=E(_1nG.a)-_1nI,_1nN=E(_1nG.b)-_1nJ,_1nO=_1nM*_1nL-_1nN*_1nK+(_1nM*_1nL-_1nN*_1nK);if(_1nO>0){var _1nP=new T(function(){var _1nQ=_1nK*_1nK+_1nL*_1nL,_1nR=_1nM*_1nM+_1nN*_1nN,_1nS=new T(function(){return _1nI+(_1nL*_1nR-_1nN*_1nQ)/_1nO;}),_1nT=new T(function(){return _1nJ+(_1nM*_1nQ-_1nK*_1nR)/_1nO;}),_1nU=B(_qU(new T1(0,_1nS),new T1(0,_1nT),new T1(0,new T(function(){var _1nV=E(_1nS),_1nW=E(_1nT);return Math.sqrt((_1nV-_1nI)*(_1nV-_1nI)+(_1nW-_1nJ)*(_1nW-_1nJ));}))));return new T3(0,_1nU.a,_1nU.b,_1nU.c);}),_1nX=B(_1bk(_1b0,_1c0,_1nP));if(!_1nX._){return E(_1lr);}else{return new T2(1,_1nX.a,new T2(1,_1nX.b,new T1(0,function(_1nY){return E(_1lr);})));}}else{return E(_1lr);}}}),_1nZ=B(_1c3(_oI,_1lp.b));if(!_1nZ._){return E(_1lq);}else{return new T2(1,_1nZ.a,new T2(1,_1nZ.b,new T1(0,function(_1o0){return E(_1lq);})));}}),_1o1=B(_1au(_1a8,_1lo));return (_1o1._==0)?E(_1jC):new T2(1,_1o1.a,new T2(1,_1o1.b,new T1(0,function(_1o2){return E(_1jC);})));}}},_1o3=new T(function(){return B(_1au(_1a8,new T(function(){return B(_1bB(E(_1jr).a));})));}),_1o4=function(_){var _1o5=nMV(_1dr),_1o6=_1o5;return new T(function(){var _1o7=new T(function(){return B(_sk(_b7,_1ds,_1d5,_1o6,_1j7,_1aL));}),_1o8=new T(function(){return B(_tf(_1o6,_1a6));}),_1o9=function(_1oa){return new F(function(){return _sk(_b7,_1ds,_1d5,_1o6,_1j7,function(_1ob){return E(_1oa);});});},_1oc=function(_1od){return new F(function(){return _1oe(E(_1od).b);});},_1of=function(_1og){return new F(function(){return A2(_1o8,E(_1og).b,_1oc);});},_1oh=function(_1oi){return new T1(0,B(_qa(_1o9,E(_1oi).b,_1of)));},_1oe=function(_1oj){return new F(function(){return A2(_1o7,_1oj,_1oh);});},_1ok=function(_1ol,_1om,_1on){return new T1(1,new T2(1,new T(function(){return B(A1(_1on,new T2(0,_7,_1om)));}),new T2(1,new T(function(){return B(_1oe(_1om));}),_6)));},_1oo=new T(function(){var _1op=new T(function(){var _1oq=new T(function(){var _1or=function(_){var _1os=rMV(_1o6),_1ot=E(_1os);return (_1ot._==0)?new T1(1,new T(function(){return B(_qq(_1ot.a));})):_2o;},_1ou=new T2(1,new T1(1,_1or),new T2(1,new T2(1,_1ag,new T1(0,_1jv)),new T1(0,function(_1ov){return E(_1o3);}))),_1ow=B(_1bk(_1b0,_1aX,new T(function(){var _1ox=new T3(0,_1ds,_1d5,_1o6),_1oy=B(_um(new T2(0,_1a7,new T2(2,_1ox,_2E)),new T2(0,_14c,new T2(2,_1ox,_2E))));return new T3(0,_1oy.a,_1oy.b,_1oy.c);})));if(!_1ow._){return E(_1ou);}else{return new T2(1,_1ow.a,new T2(1,_1ow.b,new T1(0,function(_1oz){return E(_1ou);})));}}),_1oA=B(_aT(_7,new T(function(){return B(_1cE(_1cY,_1jk));})));if(!_1oA._){return E(_1oq);}else{return new T2(1,_1oA.a,new T2(1,_1oA.b,new T1(0,function(_1oB){return E(_1oq);})));}}),_1oC=E(_1ad);if(!_1oC._){return E(_1op);}else{return new T2(1,_1oC.a,new T2(1,_1oC.b,new T1(0,function(_1oD){return E(_1op);})));}});return B(A(_1ft,[_141,_1a8,_1oo,_1ok,_1j3,_1j4]));});};return new T1(0,_1o4);};return new T1(0,_1jc);};},_1oE=function(_1oF,_1oG,_1oH){return new F(function(){return A1(_1oH,new T2(0,new T2(0,_1oF,_1oF),_1oG));});},_1oI=0,_1oJ=function(_1oK,_1oL){var _1oM=E(_1oK);if(!_1oM._){return new F(function(){return A1(_1oM.a,_1oL);});}else{var _1oN=function(_1oO,_1oP){while(1){var _1oQ=E(_1oO);if(!_1oQ._){var _1oR=B(A1(_1oQ.a,_1oL));if(!_1oR._){return new F(function(){return _1oJ(_1oP,_1oR.a);});}else{return new T2(1,_1oR.a,new T2(1,_1oR.b,_1oP));}}else{var _1oS=new T2(1,_1oQ.b,_1oP);_1oO=_1oQ.a;_1oP=_1oS;continue;}}};return new F(function(){return _1oN(_1oM.a,_1oM.b);});}},_1oT=function(_1oU,_1oV,_1oW){var _1oX=function(_){var _1oY=B(A1(_1oU,_));return new T(function(){return B(A1(_1oW,new T2(0,_1oY,_1oV)));});};return new T1(0,_1oX);},_1oZ=function(_1p0,_1p1,_1p2){var _1p3=E(_1p0);switch(_1p3._){case 0:return new F(function(){return A1(_1p2,new T2(0,_1p3.a,_1p1));});break;case 1:return new F(function(){return _1oT(_1p3.a,_1p1,_1p2);});break;case 2:var _1p4=E(_1p3.a).c,_1p5=function(_1p6){var _1p7=new T(function(){var _1p8=new T(function(){return B(A1(_1p3.b,new T(function(){return B(_qq(_1p6));})));});return B(A1(_1p2,new T2(0,_1p8,_1p1)));});return new T1(0,B(_p1(_1p4,_1p6,function(_1p9){return E(_1p7);})));};return new T1(0,B(_pd(_1p4,_1p5)));default:var _1pa=E(_1p3.a).c,_1pb=function(_1pc){var _1pd=function(_){var _1pe=B(A2(_1p3.b,new T(function(){return B(_qq(_1pc));}),_));return new T(function(){return B(A1(_1p2,new T2(0,_1pe,_1p1)));});};return new T1(0,B(_p1(_1pa,_1pc,function(_1pf){return E(new T1(0,_1pd));})));};return new T1(0,B(_pd(_1pa,_1pb)));}},_1pg=function(_1ph,_1pi,_1pj,_1pk,_1pl,_1pm,_1pn){while(1){var _1po=B((function(_1pp,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv){var _1pw=new T(function(){return 0*E(_1pq)+0*E(_1pr)+E(_1ps);}),_1px=new T(function(){return 0*E(_1pt)+0*E(_1pu)+E(_1pv);}),_1py=E(_1pp);if(!_1py._){return function(_au,_av){return new F(function(){return _3Q(_1py.a,_au,_av);});};}else{var _1pz=_1py.b,_1pA=E(_1py.a);switch(_1pA._){case 0:var _1pB=_1pq,_1pC=_1pr,_1pD=_1ps,_1pE=_1pt,_1pF=_1pu,_1pG=_1pv;_1ph=B(_1oJ(_1pz,_1pA.b));_1pi=_1pB;_1pj=_1pC;_1pk=_1pD;_1pl=_1pE;_1pm=_1pF;_1pn=_1pG;return __continue;case 1:var _1pH=function(_1pI,_1pJ){var _1pK=function(_){var _1pL=B(A1(_1pA.a,_));return new T(function(){return B(A(_1pg,[B(_1oJ(_1pz,_1pL)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv,_1pI,_1pJ]));});};return new T1(0,_1pK);};return E(_1pH);case 2:var _1pM=new T(function(){return B(A(_1pA.a,[_1pq,_1pr,_1ps,_1pt,_1pu,_1pv]));}),_1pN=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.b)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1pO=function(_1pP){var _1pQ=new T(function(){return B(A1(_1pM,_1pP));}),_1pR=function(_1pS){return new F(function(){return A1(_1pQ,function(_1pT){return new F(function(){return A2(_1pN,E(_1pT).b,_1pS);});});});};return E(_1pR);};return E(_1pO);case 3:var _1pU=new T(function(){return B(_1pg(_1pA.b,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1pV=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.c)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1pW=function(_1pX){var _1pY=new T(function(){return B(A1(_1pU,_1pX));}),_1pZ=function(_1q0){return new F(function(){return A1(_1pY,function(_1q1){return new F(function(){return A2(_1pV,E(_1q1).b,_1q0);});});});};return E(_1pZ);};return E(_1pW);case 4:var _1q2=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.h)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1q3=function(_1q4,_1q5){var _1q6=function(_1q7){return new F(function(){return A2(_1q2,E(_1q7).b,_1q5);});},_1q8=function(_1q9){var _1qa=E(_1q9),_1qb=_1qa.a,_1qc=function(_1qd){var _1qe=E(_1qd),_1qf=_1qe.a,_1qg=function(_1qh){var _1qi=E(_1qh),_1qj=_1qi.a,_1qk=function(_1ql){var _1qm=E(_1ql),_1qn=_1qm.a,_1qo=new T(function(){return E(_1qb)*E(_1pt)+E(_1qn)*E(_1pu);}),_1qp=new T(function(){return E(_1qb)*E(_1pq)+E(_1qn)*E(_1pr);}),_1qq=function(_1qr){var _1qs=E(_1qr),_1qt=_1qs.a,_1qu=new T(function(){return E(_1qf)*E(_1pt)+E(_1qt)*E(_1pu);}),_1qv=new T(function(){return E(_1qf)*E(_1pq)+E(_1qt)*E(_1pr);}),_1qw=function(_1qx){var _1qy=E(_1qx),_1qz=_1qy.a;return new F(function(){return A(_1pg,[_1pA.g,_1qp,_1qv,new T(function(){return E(_1qj)*E(_1pq)+E(_1qz)*E(_1pr)+E(_1ps);}),_1qo,_1qu,new T(function(){return E(_1qj)*E(_1pt)+E(_1qz)*E(_1pu)+E(_1pv);}),_1qy.b,_1q6]);});};return new F(function(){return _1oZ(_1pA.f,_1qs.b,_1qw);});};return new F(function(){return _1oZ(_1pA.e,_1qm.b,_1qq);});};return new F(function(){return _1oZ(_1pA.d,_1qi.b,_1qk);});};return new F(function(){return _1oZ(_1pA.c,_1qe.b,_1qg);});};return new F(function(){return _1oZ(_1pA.b,_1qa.b,_1qc);});};return new F(function(){return _1oZ(_1pA.a,_1q4,_1q8);});};return E(_1q3);case 5:var _1qA=E(_1pA.a),_1qB=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.c)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1qC=new T(function(){return 0*E(_1pt)+E(_1pu);}),_1qD=new T(function(){return E(_1pt)+0*E(_1pu);}),_1qE=new T(function(){return 0*E(_1pq)+E(_1pr);}),_1qF=new T(function(){return E(_1pq)+0*E(_1pr);}),_1qG=function(_1qH,_1qI){var _1qJ=function(_1qK){return new F(function(){return A2(_1qB,E(_1qK).b,_1qI);});},_1qL=function(_1qM){var _1qN=E(_1qM),_1qO=_1qN.a,_1qP=function(_1qQ){var _1qR=E(_1qQ),_1qS=_1qR.a;return new F(function(){return A(_1pg,[_1pA.b,_1qF,_1qE,new T(function(){return E(_1qO)*E(_1pq)+E(_1qS)*E(_1pr)+E(_1ps);}),_1qD,_1qC,new T(function(){return E(_1qO)*E(_1pt)+E(_1qS)*E(_1pu)+E(_1pv);}),_1qR.b,_1qJ]);});};return new F(function(){return _1oZ(_1qA.b,_1qN.b,_1qP);});};return new F(function(){return _1oZ(_1qA.a,_1qH,_1qL);});};return E(_1qG);case 6:var _1qT=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.c)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1qU=function(_1qV,_1qW){var _1qX=function(_1qY){return new F(function(){return A2(_1qT,E(_1qY).b,_1qW);});},_1qZ=function(_1r0){var _1r1=E(_1r0),_1r2=_1r1.a,_1r3=new T(function(){return Math.cos(E(_1r2));}),_1r4=new T(function(){return Math.sin(E(_1r2));}),_1r5=new T(function(){return  -E(_1r4);});return new F(function(){return A(_1pg,[_1pA.b,new T(function(){return E(_1r3)*E(_1pq)+E(_1r4)*E(_1pr);}),new T(function(){return E(_1r5)*E(_1pq)+E(_1r3)*E(_1pr);}),_1pw,new T(function(){return E(_1r3)*E(_1pt)+E(_1r4)*E(_1pu);}),new T(function(){return E(_1r5)*E(_1pt)+E(_1r3)*E(_1pu);}),_1px,_1r1.b,_1qX]);});};return new F(function(){return _1oZ(_1pA.a,_1qV,_1qZ);});};return E(_1qU);case 7:var _1r6=E(_1pA.a),_1r7=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.c)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1r8=function(_1r9,_1ra){var _1rb=function(_1rc){return new F(function(){return A2(_1r7,E(_1rc).b,_1ra);});},_1rd=function(_1re){var _1rf=E(_1re),_1rg=_1rf.a,_1rh=new T(function(){return E(_1rg)*E(_1pt)+0*E(_1pu);}),_1ri=new T(function(){return E(_1rg)*E(_1pq)+0*E(_1pr);}),_1rj=function(_1rk){var _1rl=E(_1rk),_1rm=_1rl.a;return new F(function(){return A(_1pg,[_1pA.b,_1ri,new T(function(){return 0*E(_1pq)+E(_1rm)*E(_1pr);}),_1pw,_1rh,new T(function(){return 0*E(_1pt)+E(_1rm)*E(_1pu);}),_1px,_1rl.b,_1rb]);});};return new F(function(){return _1oZ(_1r6.b,_1rf.b,_1rj);});};return new F(function(){return _1oZ(_1r6.a,_1r9,_1rd);});};return E(_1r8);default:var _1rn=new T(function(){return B(_1pg(_1pA.b,_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1ro=new T(function(){return B(_1pg(B(_1oJ(_1pz,_1pA.c)),_1pq,_1pr,_1ps,_1pt,_1pu,_1pv));}),_1rp=function(_1rq){var _1rr=new T(function(){return B(A1(_1rn,_1rq));}),_1rs=function(_1rt){return new F(function(){return A1(_1rr,function(_1ru){return new F(function(){return A2(_1ro,E(_1ru).b,_1rt);});});});};return E(_1rs);};return E(_1rp);}}})(_1ph,_1pi,_1pj,_1pk,_1pl,_1pm,_1pn));if(_1po!=__continue){return _1po;}}},_1rv=new T(function(){return eval("(function(e){e.width = e.width;})");}),_1rw=1,_1rx=new T1(1,_6),_1ry=new T(function(){return eval("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");}),_1rz=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_1rA=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_1rB=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_1rC=function(_1rD,_1rE,_){while(1){var _1rF=B((function(_1rG,_1rH,_){var _1rI=E(_1rG);if(!_1rI._){return _1rI.a;}else{var _1rJ=_1rI.b,_1rK=E(_1rI.a);switch(_1rK._){case 0:var _1rL=B(A2(_1rK.a,_1rH,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rK.b));_1rE=_1rM;return __continue;case 1:var _1rN=B(A1(_1rK.a,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rN));_1rE=_1rM;return __continue;case 2:var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rK.b));_1rE=_1rM;return __continue;case 3:var _1rO=B(_1rC(_1rK.b,_1rK.a,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rK.c));_1rE=_1rM;return __continue;case 4:var _1rP=_1rK.h,_1rQ=function(_1rR,_){var _1rS=function(_1rT,_){var _1rU=function(_1rV,_){var _1rW=function(_1rX,_){var _1rY=function(_1rZ,_){return new F(function(){return _1b6(_1rK.f,function(_1s0,_){var _1s1=E(_1rH),_1s2=__app1(E(_1at),_1s1),_1s3=__apply(E(_1ry),new T2(1,E(_1s0),new T2(1,E(_1rZ),new T2(1,E(_1rX),new T2(1,E(_1rV),new T2(1,E(_1rT),new T2(1,E(_1rR),new T2(1,_1s1,_6)))))))),_1s4=B(_1rC(_1rK.g,_1s1,_)),_1s5=__app1(E(_1aj),_1s1);return new F(function(){return _qQ(_);});},_);});};return new F(function(){return _1b6(_1rK.e,_1rY,_);});};return new F(function(){return _1b6(_1rK.d,_1rW,_);});};return new F(function(){return _1b6(_1rK.c,_1rU,_);});};return new F(function(){return _1b6(_1rK.b,_1rS,_);});},_1s6=E(_1rK.a);switch(_1s6._){case 0:var _1s7=B(_1rQ(_1s6.a,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rP));_1rE=_1rM;return __continue;case 1:var _1s8=B(A1(_1s6.a,_)),_1s9=B(_1rQ(_1s8,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rP));_1rE=_1rM;return __continue;case 2:var _1sa=rMV(E(E(_1s6.a).c)),_1sb=E(_1sa);if(!_1sb._){var _1sc=new T(function(){return B(A1(_1s6.b,new T(function(){return B(_qq(_1sb.a));})));},1),_1sd=B(_1rQ(_1sc,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rP));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rP));_1rE=_1rM;return __continue;}break;default:var _1se=rMV(E(E(_1s6.a).c)),_1sf=E(_1se);if(!_1sf._){var _1sg=B(A2(_1s6.b,E(_1sf.a).a,_)),_1sh=B(_1rQ(_1sg,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rP));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rP));_1rE=_1rM;return __continue;}}break;case 5:var _1si=_1rK.c,_1sj=E(_1rK.a),_1sk=function(_1sl,_){return new F(function(){return _1b6(_1sj.b,function(_1sm,_){var _1sn=E(_1rH),_1so=__app1(E(_1at),_1sn),_1sp=__app3(E(_1rz),_1sn,E(_1sl),E(_1sm)),_1sq=B(_1rC(_1rK.b,_1sn,_)),_1sr=__app1(E(_1aj),_1sn);return new F(function(){return _qQ(_);});},_);});},_1ss=E(_1sj.a);switch(_1ss._){case 0:var _1st=B(_1sk(_1ss.a,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1si));_1rE=_1rM;return __continue;case 1:var _1su=B(A1(_1ss.a,_)),_1sv=B(_1sk(_1su,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1si));_1rE=_1rM;return __continue;case 2:var _1sw=rMV(E(E(_1ss.a).c)),_1sx=E(_1sw);if(!_1sx._){var _1sy=new T(function(){return B(A1(_1ss.b,new T(function(){return B(_qq(_1sx.a));})));},1),_1sz=B(_1sk(_1sy,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1si));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1si));_1rE=_1rM;return __continue;}break;default:var _1sA=rMV(E(E(_1ss.a).c)),_1sB=E(_1sA);if(!_1sB._){var _1sC=B(A2(_1ss.b,E(_1sB.a).a,_)),_1sD=B(_1sk(_1sC,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1si));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1si));_1rE=_1rM;return __continue;}}break;case 6:var _1sE=_1rK.c,_1sF=function(_1sG,_){var _1sH=E(_1rH),_1sI=__app1(E(_1at),_1sH),_1sJ=__app2(E(_1rA),_1sH,E(_1sG)),_1sK=B(_1rC(_1rK.b,_1sH,_)),_1sL=__app1(E(_1aj),_1sH);return new F(function(){return _qQ(_);});},_1sM=E(_1rK.a);switch(_1sM._){case 0:var _1sN=B(_1sF(_1sM.a,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sE));_1rE=_1rM;return __continue;case 1:var _1sO=B(A1(_1sM.a,_)),_1sP=B(_1sF(_1sO,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sE));_1rE=_1rM;return __continue;case 2:var _1sQ=rMV(E(E(_1sM.a).c)),_1sR=E(_1sQ);if(!_1sR._){var _1sS=new T(function(){return B(A1(_1sM.b,new T(function(){return B(_qq(_1sR.a));})));},1),_1sT=B(_1sF(_1sS,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sE));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sE));_1rE=_1rM;return __continue;}break;default:var _1sU=rMV(E(E(_1sM.a).c)),_1sV=E(_1sU);if(!_1sV._){var _1sW=B(A2(_1sM.b,E(_1sV.a).a,_)),_1sX=B(_1sF(_1sW,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sE));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sE));_1rE=_1rM;return __continue;}}break;case 7:var _1sY=_1rK.c,_1sZ=E(_1rK.a),_1t0=function(_1t1,_){return new F(function(){return _1b6(_1sZ.b,function(_1t2,_){var _1t3=E(_1rH),_1t4=__app1(E(_1at),_1t3),_1t5=__app3(E(_1rB),_1t3,E(_1t1),E(_1t2)),_1t6=B(_1rC(_1rK.b,_1t3,_)),_1t7=__app1(E(_1aj),_1t3);return new F(function(){return _qQ(_);});},_);});},_1t8=E(_1sZ.a);switch(_1t8._){case 0:var _1t9=B(_1t0(_1t8.a,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sY));_1rE=_1rM;return __continue;case 1:var _1ta=B(A1(_1t8.a,_)),_1tb=B(_1t0(_1ta,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sY));_1rE=_1rM;return __continue;case 2:var _1tc=rMV(E(E(_1t8.a).c)),_1td=E(_1tc);if(!_1td._){var _1te=new T(function(){return B(A1(_1t8.b,new T(function(){return B(_qq(_1td.a));})));},1),_1tf=B(_1t0(_1te,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sY));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sY));_1rE=_1rM;return __continue;}break;default:var _1tg=rMV(E(E(_1t8.a).c)),_1th=E(_1tg);if(!_1th._){var _1ti=B(A2(_1t8.b,E(_1th.a).a,_)),_1tj=B(_1t0(_1ti,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sY));_1rE=_1rM;return __continue;}else{var _1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1sY));_1rE=_1rM;return __continue;}}break;default:var _1tk=B(_1rC(_1rK.a,_1rH,_)),_1rM=_1rH;_1rD=B(_1oJ(_1rJ,_1rK.c));_1rE=_1rM;return __continue;}}})(_1rD,_1rE,_));if(_1rF!=__continue){return _1rF;}}},_1tl=function(_1tm){return E(E(_1tm).b);},_1tn=__Z,_1to=function(_1tp,_1tq,_1tr,_1ts){var _1tt=E(_1ts);switch(_1tt._){case 0:return new T3(2,_1tq,_1tr,_1tn);case 1:return new T3(2,_1tq,_1tr,_1tt.a);default:var _1tu=_1tt.a,_1tv=_1tt.b,_1tw=_1tt.c;return new T1(1,new T(function(){if(!B(A2(_1tp,_1tq,_1tu))){return B(_1to(_1tp,_1tu,new T3(0,_1tq,_1tr,_1tv),_1tw));}else{return B(_1to(_1tp,_1tq,new T3(0,_1tu,_1tv,_1tr),_1tw));}}));}},_1tx=0,_1ty=function(_1tz,_1tA,_1tB){return new F(function(){return A1(_1tB,new T2(0,new T2(0,new T(function(){return E(_1tz).b;}),_1tz),_1tA));});},_1tC=function(_1tD,_1tE,_1tF){var _1tG=function(_1tH){var _1tI=E(_1tH),_1tJ=_1tI.b,_1tK=new T(function(){return E(_1tI.a)+E(_1tD)|0;}),_1tL=function(_){var _1tM=nMV(_q9),_1tN=_1tM;return new T(function(){var _1tO=function(_1tP){var _1tQ=new T(function(){return B(A1(_1tF,new T2(0,_7,E(_1tP).b)));});return new T1(0,B(_pd(_1tN,function(_1tR){return E(_1tQ);})));},_1tS=new T2(0,_1tK,_1tN),_1tT=function(_1tU){var _1tV=new T(function(){var _1tW=E(_1tU),_1tX=E(_1tW.c);if(!_1tX._){var _1tY=E(new T3(1,1,_1tS,E(_1tn)));}else{var _1tZ=_1tX.a,_1u0=_1tX.c,_1u1=E(_1tX.b),_1u2=E(_1tK),_1u3=E(_1u1.a);if(_1u2>=_1u3){if(_1u2!=_1u3){var _1u4=new T3(1,_1tZ+1|0,_1u1,E(B(_1to(function(_1u5,_1u6){var _1u7=E(E(_1u5).a),_1u8=E(E(_1u6).a);return (_1u7>=_1u8)?_1u7==_1u8:true;},_1tS,_1tx,_1u0))));}else{var _1u4=new T3(1,_1tZ+1|0,_1tS,E(B(_1to(function(_1u9,_1ua){var _1ub=E(E(_1u9).a),_1uc=E(E(_1ua).a);return (_1ub>=_1uc)?_1ub==_1uc:true;},_1u1,_1tx,_1u0))));}var _1ud=_1u4;}else{var _1ud=new T3(1,_1tZ+1|0,_1tS,E(B(_1to(function(_1ue,_1uf){var _1ug=E(E(_1ue).a),_1uh=E(E(_1uf).a);return (_1ug>=_1uh)?_1ug==_1uh:true;},_1u1,_1tx,_1u0))));}var _1tY=_1ud;}return new T4(0,E(_1tW.a),_1tW.b,E(_1tY),E(_1tW.d));});return function(_1ui,_1uj){return new F(function(){return A1(_1uj,new T2(0,new T2(0,_7,_1tV),_1ui));});};};return B(A(_rN,[_4l,_1tJ,_1tT,_1tJ,_1tO]));});};return new T1(0,_1tL);};return new F(function(){return A(_rN,[_4l,_1tE,_1ty,_1tE,_1tG]);});},_1uk=function(_1ul,_1um,_1un){var _1uo=function(_1up,_){var _1uq=E(_1ul),_1ur=__app1(E(_1rv),_1uq.b);return new F(function(){return _1rC(B(_1tl(_1up)),_1uq.a,_);});},_1us=function(_1ut){var _1uu=E(_1ut),_1uv=function(_){var _1uw=nMV(new T2(0,_1uu.a,_6));return new T(function(){var _1ux=new T(function(){return B(_rN(_4l,_1uw,_1oE));}),_1uy=function(_1uz){return new F(function(){return _1uA(E(_1uz).b);});},_1uB=function(_1uC){return new F(function(){return _1tC(_1rw,E(_1uC).b,_1uy);});},_1uD=function(_1uE){var _1uF=E(_1uE);return new F(function(){return A(_1pg,[B(_1tl(_1uF.a)),_1aa,_1oI,_1oI,_1oI,_1aa,_1oI,_1uF.b,_1uB]);});},_1uA=function(_1uG){return new F(function(){return A2(_1ux,_1uG,_1uD);});},_1uH=function(_1uI){var _1uJ=E(_1uI).b,_1uK=function(_){var _1uL=nMV(_1rx);return new T1(1,new T2(1,new T(function(){return B(A1(_1un,new T2(0,_7,_1uJ)));}),new T2(1,new T(function(){return B(_1uA(_1uJ));}),_6)));};return new T1(0,_1uK);};return new T1(0,B(_4t(_1uw,_1uo,_1uu.b,_1uH)));});};return new T1(0,_1uv);};return new F(function(){return _1j2(_1um,_1us);});},_1uM="deltaZ",_1uN="deltaY",_1uO="deltaX",_1uP=new T(function(){return B(unCStr(")"));}),_1uQ=new T(function(){return B(_fd(0,2,_1uP));}),_1uR=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_1uQ));}),_1uS=function(_1uT){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_fd(0,_1uT,_1uR));}))));});},_1uU=function(_1uV,_){return new T(function(){var _1uW=Number(E(_1uV)),_1uX=jsTrunc(_1uW);if(_1uX<0){return B(_1uS(_1uX));}else{if(_1uX>2){return B(_1uS(_1uX));}else{return _1uX;}}});},_1uY=0,_1uZ=new T3(0,_1uY,_1uY,_1uY),_1v0="button",_1v1=new T(function(){return eval("jsGetMouseCoords");}),_1v2=function(_1v3,_){var _1v4=E(_1v3);if(!_1v4._){return _6;}else{var _1v5=B(_1v2(_1v4.b,_));return new T2(1,new T(function(){var _1v6=Number(E(_1v4.a));return jsTrunc(_1v6);}),_1v5);}},_1v7=function(_1v8,_){var _1v9=__arr2lst(0,_1v8);return new F(function(){return _1v2(_1v9,_);});},_1va=function(_1vb,_){return new F(function(){return _1v7(E(_1vb),_);});},_1vc=function(_1vd,_){return new T(function(){var _1ve=Number(E(_1vd));return jsTrunc(_1ve);});},_1vf=new T2(0,_1vc,_1va),_1vg=function(_1vh,_){var _1vi=E(_1vh);if(!_1vi._){return _6;}else{var _1vj=B(_1vg(_1vi.b,_));return new T2(1,_1vi.a,_1vj);}},_1vk=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_1vl=new T6(0,_2o,_2p,_6,_1vk,_2o,_2o),_1vm=new T(function(){return B(_1R(_1vl));}),_1vn=function(_){return new F(function(){return die(_1vm);});},_1vo=function(_1vp){return E(E(_1vp).a);},_1vq=function(_1vr,_1vs,_1vt,_){var _1vu=__arr2lst(0,_1vt),_1vv=B(_1vg(_1vu,_)),_1vw=E(_1vv);if(!_1vw._){return new F(function(){return _1vn(_);});}else{var _1vx=E(_1vw.b);if(!_1vx._){return new F(function(){return _1vn(_);});}else{if(!E(_1vx.b)._){var _1vy=B(A3(_1vo,_1vr,_1vw.a,_)),_1vz=B(A3(_1vo,_1vs,_1vx.a,_));return new T2(0,_1vy,_1vz);}else{return new F(function(){return _1vn(_);});}}}},_1vA=function(_1vB,_1vC,_){if(E(_1vB)==7){var _1vD=__app1(E(_1v1),_1vC),_1vE=B(_1vq(_1vf,_1vf,_1vD,_)),_1vF=__get(_1vC,E(_1uO)),_1vG=__get(_1vC,E(_1uN)),_1vH=__get(_1vC,E(_1uM));return new T(function(){return new T3(0,E(_1vE),E(_2o),E(new T3(0,_1vF,_1vG,_1vH)));});}else{var _1vI=__app1(E(_1v1),_1vC),_1vJ=B(_1vq(_1vf,_1vf,_1vI,_)),_1vK=__get(_1vC,E(_1v0)),_1vL=__eq(_1vK,E(_4r));if(!E(_1vL)){var _1vM=B(_1uU(_1vK,_));return new T(function(){return new T3(0,E(_1vJ),E(new T1(1,_1vM)),E(_1uZ));});}else{return new T(function(){return new T3(0,E(_1vJ),E(_2o),E(_1uZ));});}}},_1vN=function(_1vO,_1vP,_){return new F(function(){return _1vA(_1vO,E(_1vP),_);});},_1vQ="mouseout",_1vR="mouseover",_1vS="mousemove",_1vT="mouseup",_1vU="mousedown",_1vV="dblclick",_1vW="click",_1vX="wheel",_1vY=function(_1vZ){switch(E(_1vZ)){case 0:return E(_1vW);case 1:return E(_1vV);case 2:return E(_1vU);case 3:return E(_1vT);case 4:return E(_1vS);case 5:return E(_1vR);case 6:return E(_1vQ);default:return E(_1vX);}},_1w0=new T2(0,_1vY,_1vN),_1w1=function(_1w2,_){return new T1(1,_1w2);},_1w3=new T2(0,_2E,_1w1),_1w4=function(_1w5,_1w6,_1w7){var _1w8=function(_1w9,_){return new F(function(){return _e(new T(function(){return B(A3(_1w5,_1w9,_1w6,_2H));}),_6,_);});};return new F(function(){return A1(_1w7,new T2(0,_1w8,_1w6));});},_1wa=new T2(0,_4f,_1oT),_1wb=new T2(0,_1wa,_1w4),_1wc=function(_1wd,_1we,_1wf){return new F(function(){return A1(_1wf,new T2(0,new T2(0,new T(function(){return E(E(_1wd).a);}),_1wd),_1we));});},_1wg=16,_1wh=function(_1wi,_1wj,_1wk){var _1wl=E(_1wi);if(!_1wl._){return new F(function(){return A1(_1wk,new T2(0,_6,_1wj));});}else{var _1wm=function(_1wn){var _1wo=E(_1wn);return new F(function(){return _1wh(_1wl.b,_1wo.b,function(_1wp){var _1wq=E(_1wp);return new F(function(){return A1(_1wk,new T2(0,new T2(1,_1wo.a,_1wq.a),_1wq.b));});});});};return new F(function(){return A2(E(_1wl.a).a,_1wj,_1wm);});}},_1wr=function(_1ws,_1wt,_1wu){var _1wv=E(_1ws);if(!_1wv._){return new F(function(){return A1(_1wu,new T2(0,_6,_1wt));});}else{var _1ww=E(_1wv.a),_1wx=function(_1wy){var _1wz=E(_1wy),_1wA=function(_1wB){var _1wC=E(_1wB),_1wD=_1wC.a;return new F(function(){return A1(_1wu,new T2(0,new T(function(){if(!E(_1wz.a)){return E(_1wD);}else{return new T2(1,_1ww,_1wD);}}),_1wC.b));});};return new F(function(){return _1wr(_1wv.b,_1wz.b,_1wA);});};return new F(function(){return A2(_1ww.b,_1wt,_1wx);});}},_1wE=function(_1wF,_1wG){var _1wH=E(_1wG);switch(_1wH._){case 0:return __Z;case 1:var _1wI=B(_1wE(_1wF,_1wH.a));if(!_1wI._){return __Z;}else{var _1wJ=E(_1wI.b);return new T3(1,_1wI.a,_1wJ.c,new T3(2,_1wJ.a,_1wJ.b,_1wI.c));}break;default:var _1wK=_1wH.a,_1wL=_1wH.b,_1wM=_1wH.c,_1wN=B(_1wE(_1wF,_1wM));if(!_1wN._){return new T3(1,_1wK,_1wL,new T1(1,_1wM));}else{var _1wO=_1wN.a,_1wP=_1wN.c;if(!B(A2(_1wF,_1wK,_1wO))){var _1wQ=E(_1wN.b),_1wR=_1wQ.a,_1wS=_1wQ.b;return new T3(1,_1wO,_1wQ.c,new T1(1,new T(function(){if(!B(A2(_1wF,_1wK,_1wR))){return B(_1to(_1wF,_1wR,new T3(0,_1wK,_1wL,_1wS),_1wP));}else{return B(_1to(_1wF,_1wK,new T3(0,_1wR,_1wS,_1wL),_1wP));}})));}else{return new T3(1,_1wK,_1wL,new T1(1,_1wM));}}}},_1wT=function(_1wU){var _1wV=new T(function(){var _1wW=E(_1wU),_1wX=E(_1wW.c);if(!_1wX._){var _1wY=__Z;}else{var _1wZ=B(_1wE(function(_1x0,_1x1){var _1x2=E(E(_1x0).a),_1x3=E(E(_1x1).a);return (_1x2>=_1x3)?_1x2==_1x3:true;},_1wX.c));if(!_1wZ._){var _1x4=__Z;}else{var _1x4=new T3(1,_1wX.a-1|0,_1wZ.a,E(_1wZ.c));}var _1wY=_1x4;}return new T4(0,E(_1wW.a),_1wW.b,E(_1wY),E(_1wW.d));});return function(_1x5,_1x6){return new F(function(){return A1(_1x6,new T2(0,new T2(0,_7,_1wV),_1x5));});};},_1x7=function(_1x8,_1x9,_1xa){return new F(function(){return A1(_1xa,new T2(0,new T2(0,new T(function(){var _1xb=E(E(_1x8).c);if(!_1xb._){return __Z;}else{return new T1(1,_1xb.b);}}),_1x8),_1x9));});},_1xc=function(_1xd,_1xe,_1xf){return new F(function(){return A1(_1xf,new T2(0,new T2(0,_7,new T(function(){var _1xg=E(_1xd);return new T4(0,E(_1xg.a),_1xg.b+1|0,E(_1xg.c),E(_1xg.d));})),_1xe));});},_1xh=function(_1xi,_1xj){return new T1(0,B(_1xk(_1xi)));},_1xl=function(_1xm){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1xm));}))));});},_1xn=new T(function(){return B(_1xl("w_sKgA ((), MVar WorldState) -> Action"));}),_1xo=function(_1xp){return new F(function(){return _1xh(E(_1xp).b,_1xn);});},_1xq=function(_1xr){var _1xs=E(_1xr).b;return new F(function(){return A(_rN,[_4l,_1xs,_1xc,_1xs,_1xo]);});},_1xt=function(_1xu,_1xv){var _1xw=new T(function(){return B(A2(_aW,_1xu,_7));}),_1xx=new T(function(){return B(_1xt(_1xu,_1xv));});return new F(function(){return A3(_ak,_1xu,_1xv,function(_1xy){return (!E(_1xy))?E(_1xw):E(_1xx);});});},_1xz=function(_1xA){var _1xB=E(_1xA),_1xC=function(_1xD,_1xE){var _1xF=function(_1xG){return new F(function(){return A1(_1xE,new T2(0,_ch,E(_1xG).b));});},_1xH=function(_1xI){var _1xJ=E(_1xI),_1xK=_1xJ.b,_1xL=E(_1xJ.a);if(!_1xL._){return new F(function(){return A1(_1xE,new T2(0,_5i,_1xK));});}else{var _1xM=E(_1xL.a);if(E(_1xM.a)<=E(_1xB.a)){var _1xN=new T(function(){return B(A(_rN,[_4l,_1xK,_1wT,_1xK,_1xF]));});return new T1(0,B(_p1(_1xM.b,_7,function(_1xO){return E(_1xN);})));}else{return new F(function(){return A1(_1xE,new T2(0,_5i,_1xK));});}}};return new F(function(){return A(_rN,[_4l,_1xD,_1x7,_1xD,_1xH]);});};return new F(function(){return A(_1xt,[_4f,_1xC,_1xB.b,_1xq]);});},_1xP=function(_1xQ){var _1xR=E(_1xQ).b;return new F(function(){return A(_rN,[_4l,_1xR,_1ty,_1xR,_1xz]);});},_1xS=function(_1xT){var _1xU=E(_1xT),_1xV=_1xU.b,_1xW=function(_1xX,_1xY,_1xZ){return new F(function(){return A1(_1xZ,new T2(0,new T2(0,_7,new T(function(){var _1y0=E(_1xX);return new T4(0,E(_1xU.a),_1y0.b,E(_1y0.c),E(_1y0.d));})),_1xY));});};return new F(function(){return A(_rN,[_4l,_1xV,_1xW,_1xV,_1xP]);});},_1y1=function(_1y2){var _1y3=E(_1y2),_1y4=_1y3.a;return new F(function(){return _1wh(_1y4,_1y3.b,function(_1y5){return new F(function(){return _1wr(_1y4,E(_1y5).b,_1xS);});});});},_1xk=function(_1y6){var _1y7=new T(function(){return B(A(_rN,[_4l,_1y6,_1wc,_1y6,_1y1]));});return new F(function(){return _q0(_1wg,function(_1y8){return E(_1y7);});});},_1y9=2,_1ya=4,_1yb=3,_1yc=function(_1yd,_1ye,_1yf){return new F(function(){return A1(_1yf,new T2(0,new T2(0,new T(function(){return E(E(E(_1yd).d).b);}),_1yd),_1ye));});},_1yg=new T(function(){return eval("document");}),_1yh=new T1(0,_5i),_1yi=new T1(0,_ch),_1yj=new T1(1,_6),_1yk=__Z,_1yl=new T0(2),_1ym=new T2(0,_q8,_1yl),_1yn=new T4(0,E(_6),0,E(_1yk),E(_1ym)),_1yo=new T2(0,_1yn,_6),_1yp=function(_1yq){return E(E(_1yq).a);},_1yr=function(_1ys){return E(E(_1ys).b);},_1yt=function(_1yu){return E(E(_1yu).a);},_1yv=function(_){return new F(function(){return nMV(_2o);});},_1yw=new T(function(){return B(_4n(_1yv));}),_1yx=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1yy=function(_1yz,_1yA,_1yB,_1yC,_1yD,_1yE){var _1yF=B(_pr(_1yz)),_1yG=B(_pt(_1yF)),_1yH=new T(function(){return B(_px(_1yF));}),_1yI=new T(function(){return B(_aW(_1yG));}),_1yJ=new T(function(){return B(A2(_1yp,_1yA,_1yC));}),_1yK=new T(function(){return B(A2(_1yt,_1yB,_1yD));}),_1yL=function(_1yM){return new F(function(){return A1(_1yI,new T3(0,_1yK,_1yJ,_1yM));});},_1yN=function(_1yO){var _1yP=new T(function(){var _1yQ=new T(function(){var _1yR=__createJSFunc(2,function(_1yS,_){var _1yT=B(A2(E(_1yO),_1yS,_));return _4r;}),_1yU=_1yR;return function(_){return new F(function(){return __app3(E(_1yx),E(_1yJ),E(_1yK),_1yU);});};});return B(A1(_1yH,_1yQ));});return new F(function(){return A3(_ak,_1yG,_1yP,_1yL);});},_1yV=new T(function(){var _1yW=new T(function(){return B(_px(_1yF));}),_1yX=function(_1yY){var _1yZ=new T(function(){return B(A1(_1yW,function(_){var _=wMV(E(_1yw),new T1(1,_1yY));return new F(function(){return A(_1yr,[_1yB,_1yD,_1yY,_]);});}));});return new F(function(){return A3(_ak,_1yG,_1yZ,_1yE);});};return B(A2(_pz,_1yz,_1yX));});return new F(function(){return A3(_ak,_1yG,_1yV,_1yN);});},_1z0=function(_1z1,_1z2){return new F(function(){return A1(_1z2,new T2(0,_7,_1z1));});},_1z3=function(_1z4,_1z5){return function(_){var _1z6=nMV(_1yo),_1z7=_1z6,_1z8=function(_1z9){return new F(function(){return A1(_1z5,E(_1z9).a);});},_1za=function(_1zb){return new F(function(){return A2(_1z4,E(_1zb).b,_1z8);});},_1zc=function(_){var _1zd=nMV(_1yj),_1ze=_1zd,_1zf=new T(function(){var _1zg=function(_1zh){return new F(function(){return _1zi(E(_1zh).b);});},_1zi=function(_1zj){var _1zk=function(_1zl){var _1zm=function(_1zn){var _1zo=E(_1zn),_1zp=_1zo.b,_1zq=E(_1zl),_1zr=function(_1zs,_1zt,_1zu){var _1zv=function(_1zw,_1zx){while(1){var _1zy=B((function(_1zz,_1zA){var _1zB=E(_1zA);switch(_1zB._){case 0:_1zw=new T(function(){return B(_1zv(_1zz,_1zB.d));});_1zx=_1zB.c;return __continue;case 1:var _1zC=new T(function(){return B(_1dt(_4l,_1zB.b,_1zs));}),_1zD=function(_1zE){var _1zF=new T(function(){return B(A1(_1zC,_1zE));}),_1zG=function(_1zH){return new F(function(){return A1(_1zF,function(_1zI){return new F(function(){return A2(_1zz,E(_1zI).b,_1zH);});});});};return E(_1zG);};return E(_1zD);default:return E(_1zz);}})(_1zw,_1zx));if(_1zy!=__continue){return _1zy;}}},_1zJ=E(_1zo.a);if(!_1zJ._){var _1zK=_1zJ.c,_1zL=_1zJ.d;if(_1zJ.b>=0){return new F(function(){return A(_1zv,[new T(function(){return B(_1zv(_1z0,_1zL));}),_1zK,_1zt,_1zu]);});}else{return new F(function(){return A(_1zv,[new T(function(){return B(_1zv(_1z0,_1zK));}),_1zL,_1zt,_1zu]);});}}else{return new F(function(){return A(_1zv,[_1z0,_1zJ,_1zt,_1zu]);});}};switch(E(_1zq.a)){case 2:return new F(function(){return _1zr(_1yi,_1zp,_1zg);});break;case 3:return new F(function(){return _1zr(_1yh,_1zp,_1zg);});break;case 4:var _1zM=new T(function(){return E(E(_1zq.b).a);});return new F(function(){return _1zr(new T1(1,new T2(0,new T(function(){return E(E(_1zM).a);}),new T(function(){return E(E(_1zM).b);}))),_1zp,_1zg);});break;default:return new F(function(){return _1zi(_1zp);});}};return new F(function(){return A(_rN,[_4l,_1zj,_1yc,_1zj,_1zm]);});};return new T1(0,B(_pd(_1ze,_1zk)));};return B(_1zi(_1z7));}),_1zN=new T(function(){var _1zO=new T(function(){return B(_1yy(_1wb,_1w3,_1w0,_1yg,_1ya,function(_1zP){return new F(function(){return _1dt(_4l,_1ze,new T2(0,_1ya,_1zP));});}));}),_1zQ=new T(function(){return B(_1yy(_1wb,_1w3,_1w0,_1yg,_1yb,function(_1zR){return new F(function(){return _1dt(_4l,_1ze,new T2(0,_1yb,_1zR));});}));}),_1zS=function(_1zT){return new F(function(){return A2(_1zQ,E(_1zT).b,_1za);});};return B(A(_1yy,[_1wb,_1w3,_1w0,_1yg,_1y9,function(_1zU){return new F(function(){return _1dt(_4l,_1ze,new T2(0,_1y9,_1zU));});},_1z7,function(_1zV){return new F(function(){return A2(_1zO,E(_1zV).b,_1zS);});}]));});return new T1(1,new T2(1,_1zN,new T2(1,_1zf,_6)));};return new T1(1,new T2(1,new T1(0,_1zc),new T2(1,new T(function(){return new T1(0,B(_1xk(_1z7)));}),_6)));};},_1zW=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1zX=function(_1zY,_1zZ){var _1A0=function(_){var _1A1=__app1(E(_1zW),E(_1zZ)),_1A2=__eq(_1A1,E(_4r));return (E(_1A2)==0)?new T1(1,_1A1):_2o;};return new F(function(){return A2(_px,_1zY,_1A0);});},_1A3=new T(function(){return B(unCStr("Canvas not found!"));}),_1A4=new T(function(){return B(err(_1A3));}),_1A5="canvas",_1A6=new T(function(){return eval("(Util.onload)");}),_1A7=function(_){var _1A8=__app1(E(_1A6),E(_4r)),_1A9=B(A3(_1zX,_2G,_1A5,_)),_1Aa=E(_1A9);if(!_1Aa._){return E(_1A4);}else{var _1Ab=E(_1Aa.a),_1Ac=__app1(E(_1),_1Ab);if(!_1Ac){return E(_1A4);}else{var _1Ad=__app1(E(_0),_1Ab),_1Ae=_1Ad,_1Af=new T(function(){return new T1(0,B(_1z3(function(_1Ag,_1Ah){return new T1(0,B(_1uk(new T2(0,_1Ae,_1Ab),_1Ag,_1Ah)));},_oZ)));});return new F(function(){return _e(_1Af,_6,_);});}}},_1Ai=function(_){return new F(function(){return _1A7(_);});};
var hasteMain = function() {B(A(_1Ai, [0]));};window.onload = hasteMain;