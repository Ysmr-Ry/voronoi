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

var _0=new T(function(){return eval("(function(e){return e.getContext(\'2d\');})");}),_1=new T(function(){return eval("(function(e){return !!e.getContext;})");}),_2=function(_3,_4){var _5=E(_3);return (_5._==0)?E(_4):new T2(1,_5.a,new T(function(){return B(_2(_5.b,_4));}));},_6=__Z,_7=0,_8=function(_9,_){while(1){var _a=E(_9);if(!_a._){return _7;}else{var _b=_a.b,_c=E(_a.a);switch(_c._){case 0:var _d=B(A1(_c.a,_));_9=B(_2(_b,new T2(1,_d,_6)));continue;case 1:_9=B(_2(_b,_c.a));continue;default:_9=_b;continue;}}}},_e=function(_f,_g,_){var _h=E(_f);switch(_h._){case 0:var _i=B(A1(_h.a,_));return new F(function(){return _8(B(_2(_g,new T2(1,_i,_6))),_);});break;case 1:return new F(function(){return _8(B(_2(_g,_h.a)),_);});break;default:return new F(function(){return _8(_g,_);});}},_j=function(_k,_l,_){var _m=B(A1(_k,_)),_n=B(A1(_l,_));return _m;},_o=function(_p,_q,_){var _r=B(A1(_p,_)),_s=B(A1(_q,_));return new T(function(){return B(A1(_r,_s));});},_t=function(_u,_v,_){var _w=B(A1(_v,_));return _u;},_x=function(_y,_z,_){var _A=B(A1(_z,_));return new T(function(){return B(A1(_y,_A));});},_B=new T2(0,_x,_t),_C=function(_D,_){return _D;},_E=function(_F,_G,_){var _H=B(A1(_F,_));return new F(function(){return A1(_G,_);});},_I=new T5(0,_B,_C,_o,_E,_j),_J=new T(function(){return B(unCStr("base"));}),_K=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_L=new T(function(){return B(unCStr("IOException"));}),_M=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_J,_K,_L),_N=new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_M,_6,_6),_O=function(_P){return E(_N);},_Q=function(_R){return E(E(_R).a);},_S=function(_T,_U,_V){var _W=B(A1(_T,_)),_X=B(A1(_U,_)),_Y=hs_eqWord64(_W.a,_X.a);if(!_Y){return __Z;}else{var _Z=hs_eqWord64(_W.b,_X.b);return (!_Z)?__Z:new T1(1,_V);}},_10=function(_11){var _12=E(_11);return new F(function(){return _S(B(_Q(_12.a)),_O,_12.b);});},_13=new T(function(){return B(unCStr(": "));}),_14=new T(function(){return B(unCStr(")"));}),_15=new T(function(){return B(unCStr(" ("));}),_16=new T(function(){return B(unCStr("interrupted"));}),_17=new T(function(){return B(unCStr("system error"));}),_18=new T(function(){return B(unCStr("unsatisified constraints"));}),_19=new T(function(){return B(unCStr("user error"));}),_1a=new T(function(){return B(unCStr("permission denied"));}),_1b=new T(function(){return B(unCStr("illegal operation"));}),_1c=new T(function(){return B(unCStr("end of file"));}),_1d=new T(function(){return B(unCStr("resource exhausted"));}),_1e=new T(function(){return B(unCStr("resource busy"));}),_1f=new T(function(){return B(unCStr("does not exist"));}),_1g=new T(function(){return B(unCStr("already exists"));}),_1h=new T(function(){return B(unCStr("resource vanished"));}),_1i=new T(function(){return B(unCStr("timeout"));}),_1j=new T(function(){return B(unCStr("unsupported operation"));}),_1k=new T(function(){return B(unCStr("hardware fault"));}),_1l=new T(function(){return B(unCStr("inappropriate type"));}),_1m=new T(function(){return B(unCStr("invalid argument"));}),_1n=new T(function(){return B(unCStr("failed"));}),_1o=new T(function(){return B(unCStr("protocol error"));}),_1p=function(_1q,_1r){switch(E(_1q)){case 0:return new F(function(){return _2(_1g,_1r);});break;case 1:return new F(function(){return _2(_1f,_1r);});break;case 2:return new F(function(){return _2(_1e,_1r);});break;case 3:return new F(function(){return _2(_1d,_1r);});break;case 4:return new F(function(){return _2(_1c,_1r);});break;case 5:return new F(function(){return _2(_1b,_1r);});break;case 6:return new F(function(){return _2(_1a,_1r);});break;case 7:return new F(function(){return _2(_19,_1r);});break;case 8:return new F(function(){return _2(_18,_1r);});break;case 9:return new F(function(){return _2(_17,_1r);});break;case 10:return new F(function(){return _2(_1o,_1r);});break;case 11:return new F(function(){return _2(_1n,_1r);});break;case 12:return new F(function(){return _2(_1m,_1r);});break;case 13:return new F(function(){return _2(_1l,_1r);});break;case 14:return new F(function(){return _2(_1k,_1r);});break;case 15:return new F(function(){return _2(_1j,_1r);});break;case 16:return new F(function(){return _2(_1i,_1r);});break;case 17:return new F(function(){return _2(_1h,_1r);});break;default:return new F(function(){return _2(_16,_1r);});}},_1s=new T(function(){return B(unCStr("}"));}),_1t=new T(function(){return B(unCStr("{handle: "));}),_1u=function(_1v,_1w,_1x,_1y,_1z,_1A){var _1B=new T(function(){var _1C=new T(function(){var _1D=new T(function(){var _1E=E(_1y);if(!_1E._){return E(_1A);}else{var _1F=new T(function(){return B(_2(_1E,new T(function(){return B(_2(_14,_1A));},1)));},1);return B(_2(_15,_1F));}},1);return B(_1p(_1w,_1D));}),_1G=E(_1x);if(!_1G._){return E(_1C);}else{return B(_2(_1G,new T(function(){return B(_2(_13,_1C));},1)));}}),_1H=E(_1z);if(!_1H._){var _1I=E(_1v);if(!_1I._){return E(_1B);}else{var _1J=E(_1I.a);if(!_1J._){var _1K=new T(function(){var _1L=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1L));},1);return new F(function(){return _2(_1t,_1K);});}else{var _1M=new T(function(){var _1N=new T(function(){return B(_2(_1s,new T(function(){return B(_2(_13,_1B));},1)));},1);return B(_2(_1J.a,_1N));},1);return new F(function(){return _2(_1t,_1M);});}}}else{return new F(function(){return _2(_1H.a,new T(function(){return B(_2(_13,_1B));},1));});}},_1O=function(_1P){var _1Q=E(_1P);return new F(function(){return _1u(_1Q.a,_1Q.b,_1Q.c,_1Q.d,_1Q.f,_6);});},_1R=function(_1S){return new T2(0,_1T,_1S);},_1U=function(_1V,_1W,_1X){var _1Y=E(_1W);return new F(function(){return _1u(_1Y.a,_1Y.b,_1Y.c,_1Y.d,_1Y.f,_1X);});},_1Z=function(_20,_21){var _22=E(_20);return new F(function(){return _1u(_22.a,_22.b,_22.c,_22.d,_22.f,_21);});},_23=44,_24=93,_25=91,_26=function(_27,_28,_29){var _2a=E(_28);if(!_2a._){return new F(function(){return unAppCStr("[]",_29);});}else{var _2b=new T(function(){var _2c=new T(function(){var _2d=function(_2e){var _2f=E(_2e);if(!_2f._){return E(new T2(1,_24,_29));}else{var _2g=new T(function(){return B(A2(_27,_2f.a,new T(function(){return B(_2d(_2f.b));})));});return new T2(1,_23,_2g);}};return B(_2d(_2a.b));});return B(A2(_27,_2a.a,_2c));});return new T2(1,_25,_2b);}},_2h=function(_2i,_2j){return new F(function(){return _26(_1Z,_2i,_2j);});},_2k=new T3(0,_1U,_1O,_2h),_1T=new T(function(){return new T5(0,_O,_2k,_1R,_10,_1O);}),_2l=new T(function(){return E(_1T);}),_2m=function(_2n){return E(E(_2n).c);},_2o=__Z,_2p=7,_2q=function(_2r){return new T6(0,_2o,_2p,_6,_2r,_2o,_2o);},_2s=function(_2t,_){var _2u=new T(function(){return B(A2(_2m,_2l,new T(function(){return B(A1(_2q,_2t));})));});return new F(function(){return die(_2u);});},_2v=function(_2w,_){return new F(function(){return _2s(_2w,_);});},_2x=function(_2y){return new F(function(){return A1(_2v,_2y);});},_2z=function(_2A,_2B,_){var _2C=B(A1(_2A,_));return new F(function(){return A2(_2B,_2C,_);});},_2D=new T5(0,_I,_2z,_E,_C,_2x),_2E=function(_2F){return E(_2F);},_2G=new T2(0,_2D,_2E),_2H=function(_2I){var _2J=E(_2I);return new T0(2);},_2K=function(_2L,_2M,_2N){return new T1(1,new T2(1,new T(function(){return B(A1(_2N,new T2(0,_7,_2M)));}),new T2(1,new T(function(){return B(A2(_2L,_2M,_2H));}),_6)));},_2O=function(_2P,_2Q,_2R){var _2S=new T(function(){return B(A1(_2P,_2R));}),_2T=function(_2U){var _2V=function(_2W){var _2X=E(_2W);return new F(function(){return A2(_2Q,_2X.b,function(_2Y){return new F(function(){return A1(_2U,new T2(0,_2X.a,E(_2Y).b));});});});};return new F(function(){return A1(_2S,_2V);});};return E(_2T);},_2Z=function(_30,_31,_32){var _33=new T(function(){return B(A1(_30,_32));}),_34=function(_35){var _36=function(_37){return new F(function(){return A1(_35,E(_37));});};return new F(function(){return A1(_33,function(_38){return new F(function(){return A2(_31,E(_38).b,_36);});});});};return E(_34);},_39=function(_3a,_3b,_3c){var _3d=new T(function(){return B(A1(_3a,_3c));}),_3e=function(_3f){var _3g=function(_3h){var _3i=E(_3h),_3j=function(_3k){var _3l=E(_3k);return new F(function(){return A1(_3f,new T2(0,new T(function(){return B(A1(_3i.a,_3l.a));}),_3l.b));});};return new F(function(){return A2(_3b,_3i.b,_3j);});};return new F(function(){return A1(_3d,_3g);});};return E(_3e);},_3m=function(_3n,_3o,_3p){return new F(function(){return _39(_3n,_3o,_3p);});},_3q=function(_3r,_3s,_3t){var _3u=new T(function(){return B(A1(_3s,_3t));}),_3v=function(_3w){var _3x=function(_3y){return new F(function(){return A1(_3w,new T(function(){return new T2(0,_3r,E(_3y).b);}));});};return new F(function(){return A1(_3u,_3x);});};return E(_3v);},_3z=function(_3A,_3B,_3C){var _3D=new T(function(){return B(A1(_3B,_3C));}),_3E=function(_3F){var _3G=function(_3H){var _3I=new T(function(){var _3J=E(_3H);return new T2(0,new T(function(){return B(A1(_3A,_3J.a));}),_3J.b);});return new F(function(){return A1(_3F,_3I);});};return new F(function(){return A1(_3D,_3G);});};return E(_3E);},_3K=function(_3n,_3o,_3p){return new F(function(){return _3z(_3n,_3o,_3p);});},_3L=new T2(0,_3K,_3q),_3M=function(_3N,_3O,_3P){return new F(function(){return A1(_3P,new T2(0,_3N,_3O));});},_3Q=function(_3n,_3o,_3p){return new F(function(){return _3M(_3n,_3o,_3p);});},_3R=new T5(0,_3L,_3Q,_3m,_2Z,_2O),_3S=function(_3T,_3U,_3V){var _3W=new T(function(){return B(A1(_3T,_3V));}),_3X=function(_3Y){return new F(function(){return A1(_3W,function(_3Z){return new F(function(){return A2(_3U,E(_3Z).b,_3Y);});});});};return E(_3X);},_40=function(_3n,_3o,_3p){return new F(function(){return _3S(_3n,_3o,_3p);});},_41=function(_42,_43,_44){var _45=new T(function(){return B(A1(_42,_44));}),_46=function(_47){return new F(function(){return A1(_45,function(_48){var _49=E(_48);return new F(function(){return A3(_43,_49.a,_49.b,_47);});});});};return E(_46);},_4a=function(_3n,_3o,_3p){return new F(function(){return _41(_3n,_3o,_3p);});},_4b=function(_4c,_4d){return new F(function(){return err(_4c);});},_4e=function(_3o,_3p){return new F(function(){return _4b(_3o,_3p);});},_4f=new T5(0,_3R,_4a,_40,_3Q,_4e),_4g=function(_4h,_4i,_4j){return new F(function(){return A1(_4h,function(_4k){return new F(function(){return A1(_4j,new T2(0,_4k,_4i));});});});},_4l=new T3(0,_4f,_4g,_2K),_4m=function(_){return new F(function(){return __jsNull();});},_4n=function(_4o){var _4p=B(A1(_4o,_));return E(_4p);},_4q=new T(function(){return B(_4n(_4m));}),_4r=new T(function(){return E(_4q);}),_4s=new T(function(){return eval("window.requestAnimationFrame");}),_4t=function(_4u,_4v,_4w,_4x){return function(_){var _4y=E(_4u),_4z=rMV(_4y),_4A=E(_4z);if(!_4A._){var _4B=B(A2(_4v,_4A.a,_)),_4C=function(_4D,_){var _4E=function(_){var _4F=rMV(_4y),_4G=function(_,_4H){var _4I=function(_){var _4J=__createJSFunc(2,function(_4K,_){var _4L=B(_4M(_,_));return _4r;}),_4N=__app1(E(_4s),_4J);return _7;},_4O=E(_4H);if(!_4O._){return new F(function(){return _4I(_);});}else{var _4P=B(A2(_4v,_4O.a,_));return new F(function(){return _4I(_);});}},_4Q=E(_4F);if(!_4Q._){return new F(function(){return _4G(_,new T1(1,_4Q.a));});}else{return new F(function(){return _4G(_,_2o);});}},_4M=function(_4R,_){return new F(function(){return _4E(_);});},_4S=B(_4M(_,_));return _4r;},_4T=__createJSFunc(2,E(_4C)),_4U=__app1(E(_4s),_4T);return new T(function(){return B(A1(_4x,new T2(0,_7,_4w)));});}else{var _4V=function(_4W,_){var _4X=function(_){var _4Y=rMV(_4y),_4Z=function(_,_50){var _51=function(_){var _52=__createJSFunc(2,function(_53,_){var _54=B(_55(_,_));return _4r;}),_56=__app1(E(_4s),_52);return _7;},_57=E(_50);if(!_57._){return new F(function(){return _51(_);});}else{var _58=B(A2(_4v,_57.a,_));return new F(function(){return _51(_);});}},_59=E(_4Y);if(!_59._){return new F(function(){return _4Z(_,new T1(1,_59.a));});}else{return new F(function(){return _4Z(_,_2o);});}},_55=function(_5a,_){return new F(function(){return _4X(_);});},_5b=B(_55(_,_));return _4r;},_5c=__createJSFunc(2,E(_4V)),_5d=__app1(E(_4s),_5c);return new T(function(){return B(A1(_4x,new T2(0,_7,_4w)));});}};},_5e=function(_){return _7;},_5f=function(_5g,_5h,_){return new F(function(){return _5e(_);});},_5i=false,_5j=function(_){return _5i;},_5k=function(_5l,_){return new F(function(){return _5j(_);});},_5m=function(_5n,_5o){var _5p=E(_5n),_5q=E(_5o);return (_5p.a!=_5q.a)?false:(_5p.b!=_5q.b)?false:_5p.c==_5q.c;},_5r=new T1(0,1),_5s=function(_5t,_5u){var _5v=E(_5t);if(!_5v._){var _5w=_5v.a,_5x=E(_5u);if(!_5x._){var _5y=_5x.a;return (_5w!=_5y)?(_5w>_5y)?2:0:1;}else{var _5z=I_compareInt(_5x.a,_5w);return (_5z<=0)?(_5z>=0)?1:2:0;}}else{var _5A=_5v.a,_5B=E(_5u);if(!_5B._){var _5C=I_compareInt(_5A,_5B.a);return (_5C>=0)?(_5C<=0)?1:2:0;}else{var _5D=I_compare(_5A,_5B.a);return (_5D>=0)?(_5D<=0)?1:2:0;}}},_5E=new T(function(){return B(unCStr("base"));}),_5F=new T(function(){return B(unCStr("GHC.Exception"));}),_5G=new T(function(){return B(unCStr("ArithException"));}),_5H=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_5E,_5F,_5G),_5I=new T5(0,new Long(4194982440,719304104,true),new Long(3110813675,1843557400,true),_5H,_6,_6),_5J=function(_5K){return E(_5I);},_5L=function(_5M){var _5N=E(_5M);return new F(function(){return _S(B(_Q(_5N.a)),_5J,_5N.b);});},_5O=new T(function(){return B(unCStr("Ratio has zero denominator"));}),_5P=new T(function(){return B(unCStr("denormal"));}),_5Q=new T(function(){return B(unCStr("divide by zero"));}),_5R=new T(function(){return B(unCStr("loss of precision"));}),_5S=new T(function(){return B(unCStr("arithmetic underflow"));}),_5T=new T(function(){return B(unCStr("arithmetic overflow"));}),_5U=function(_5V,_5W){switch(E(_5V)){case 0:return new F(function(){return _2(_5T,_5W);});break;case 1:return new F(function(){return _2(_5S,_5W);});break;case 2:return new F(function(){return _2(_5R,_5W);});break;case 3:return new F(function(){return _2(_5Q,_5W);});break;case 4:return new F(function(){return _2(_5P,_5W);});break;default:return new F(function(){return _2(_5O,_5W);});}},_5X=function(_5Y){return new F(function(){return _5U(_5Y,_6);});},_5Z=function(_60,_61,_62){return new F(function(){return _5U(_61,_62);});},_63=function(_64,_65){return new F(function(){return _26(_5U,_64,_65);});},_66=new T3(0,_5Z,_5X,_63),_67=new T(function(){return new T5(0,_5J,_66,_68,_5L,_5X);}),_68=function(_69){return new T2(0,_67,_69);},_6a=3,_6b=new T(function(){return B(_68(_6a));}),_6c=new T(function(){return die(_6b);}),_6d=function(_6e,_6f){var _6g=E(_6e);return (_6g._==0)?_6g.a*Math.pow(2,_6f):I_toNumber(_6g.a)*Math.pow(2,_6f);},_6h=function(_6i,_6j){var _6k=E(_6i);if(!_6k._){var _6l=_6k.a,_6m=E(_6j);return (_6m._==0)?_6l==_6m.a:(I_compareInt(_6m.a,_6l)==0)?true:false;}else{var _6n=_6k.a,_6o=E(_6j);return (_6o._==0)?(I_compareInt(_6n,_6o.a)==0)?true:false:(I_compare(_6n,_6o.a)==0)?true:false;}},_6p=function(_6q){var _6r=E(_6q);if(!_6r._){return E(_6r.a);}else{return new F(function(){return I_toInt(_6r.a);});}},_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v._){var _6w=_6v.a,_6x=E(_6u);if(!_6x._){var _6y=_6x.a,_6z=addC(_6w,_6y);if(!E(_6z.b)){return new T1(0,_6z.a);}else{_6t=new T1(1,I_fromInt(_6w));_6u=new T1(1,I_fromInt(_6y));continue;}}else{_6t=new T1(1,I_fromInt(_6w));_6u=_6x;continue;}}else{var _6A=E(_6u);if(!_6A._){_6t=_6v;_6u=new T1(1,I_fromInt(_6A.a));continue;}else{return new T1(1,I_add(_6v.a,_6A.a));}}}},_6B=function(_6C,_6D){while(1){var _6E=E(_6C);if(!_6E._){var _6F=E(_6E.a);if(_6F==(-2147483648)){_6C=new T1(1,I_fromInt(-2147483648));continue;}else{var _6G=E(_6D);if(!_6G._){var _6H=_6G.a;return new T2(0,new T1(0,quot(_6F,_6H)),new T1(0,_6F%_6H));}else{_6C=new T1(1,I_fromInt(_6F));_6D=_6G;continue;}}}else{var _6I=E(_6D);if(!_6I._){_6C=_6E;_6D=new T1(1,I_fromInt(_6I.a));continue;}else{var _6J=I_quotRem(_6E.a,_6I.a);return new T2(0,new T1(1,_6J.a),new T1(1,_6J.b));}}}},_6K=new T1(0,0),_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O._){_6M=new T1(1,I_fromInt(_6O.a));continue;}else{return new T1(1,I_shiftLeft(_6O.a,_6N));}}},_6P=function(_6Q,_6R,_6S){if(!B(_6h(_6S,_6K))){var _6T=B(_6B(_6R,_6S)),_6U=_6T.a;switch(B(_5s(B(_6L(_6T.b,1)),_6S))){case 0:return new F(function(){return _6d(_6U,_6Q);});break;case 1:if(!(B(_6p(_6U))&1)){return new F(function(){return _6d(_6U,_6Q);});}else{return new F(function(){return _6d(B(_6s(_6U,_5r)),_6Q);});}break;default:return new F(function(){return _6d(B(_6s(_6U,_5r)),_6Q);});}}else{return E(_6c);}},_6V=function(_6W,_6X){var _6Y=E(_6W);if(!_6Y._){var _6Z=_6Y.a,_70=E(_6X);return (_70._==0)?_6Z>_70.a:I_compareInt(_70.a,_6Z)<0;}else{var _71=_6Y.a,_72=E(_6X);return (_72._==0)?I_compareInt(_71,_72.a)>0:I_compare(_71,_72.a)>0;}},_73=new T1(0,1),_74=function(_75,_76){var _77=E(_75);if(!_77._){var _78=_77.a,_79=E(_76);return (_79._==0)?_78<_79.a:I_compareInt(_79.a,_78)>0;}else{var _7a=_77.a,_7b=E(_76);return (_7b._==0)?I_compareInt(_7a,_7b.a)<0:I_compare(_7a,_7b.a)<0;}},_7c=new T(function(){return B(unCStr("base"));}),_7d=new T(function(){return B(unCStr("Control.Exception.Base"));}),_7e=new T(function(){return B(unCStr("PatternMatchFail"));}),_7f=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7c,_7d,_7e),_7g=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_7f,_6,_6),_7h=function(_7i){return E(_7g);},_7j=function(_7k){var _7l=E(_7k);return new F(function(){return _S(B(_Q(_7l.a)),_7h,_7l.b);});},_7m=function(_7n){return E(E(_7n).a);},_7o=function(_7p){return new T2(0,_7q,_7p);},_7r=function(_7s,_7t){return new F(function(){return _2(E(_7s).a,_7t);});},_7u=function(_7v,_7w){return new F(function(){return _26(_7r,_7v,_7w);});},_7x=function(_7y,_7z,_7A){return new F(function(){return _2(E(_7z).a,_7A);});},_7B=new T3(0,_7x,_7m,_7u),_7q=new T(function(){return new T5(0,_7h,_7B,_7o,_7j,_7m);}),_7C=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_7D=function(_7E,_7F){return new F(function(){return die(new T(function(){return B(A2(_2m,_7F,_7E));}));});},_7G=function(_7H,_69){return new F(function(){return _7D(_7H,_69);});},_7I=function(_7J,_7K){var _7L=E(_7K);if(!_7L._){return new T2(0,_6,_6);}else{var _7M=_7L.a;if(!B(A1(_7J,_7M))){return new T2(0,_6,_7L);}else{var _7N=new T(function(){var _7O=B(_7I(_7J,_7L.b));return new T2(0,_7O.a,_7O.b);});return new T2(0,new T2(1,_7M,new T(function(){return E(E(_7N).a);})),new T(function(){return E(E(_7N).b);}));}}},_7P=32,_7Q=new T(function(){return B(unCStr("\n"));}),_7R=function(_7S){return (E(_7S)==124)?false:true;},_7T=function(_7U,_7V){var _7W=B(_7I(_7R,B(unCStr(_7U)))),_7X=_7W.a,_7Y=function(_7Z,_80){var _81=new T(function(){var _82=new T(function(){return B(_2(_7V,new T(function(){return B(_2(_80,_7Q));},1)));});return B(unAppCStr(": ",_82));},1);return new F(function(){return _2(_7Z,_81);});},_83=E(_7W.b);if(!_83._){return new F(function(){return _7Y(_7X,_6);});}else{if(E(_83.a)==124){return new F(function(){return _7Y(_7X,new T2(1,_7P,_83.b));});}else{return new F(function(){return _7Y(_7X,_6);});}}},_84=function(_85){return new F(function(){return _7G(new T1(0,new T(function(){return B(_7T(_85,_7C));})),_7q);});},_86=function(_87){var _88=function(_89,_8a){while(1){if(!B(_74(_89,_87))){if(!B(_6V(_89,_87))){if(!B(_6h(_89,_87))){return new F(function(){return _84("GHC/Integer/Type.lhs:(555,5)-(557,32)|function l2");});}else{return E(_8a);}}else{return _8a-1|0;}}else{var _8b=B(_6L(_89,1)),_8c=_8a+1|0;_89=_8b;_8a=_8c;continue;}}};return new F(function(){return _88(_73,0);});},_8d=function(_8e){var _8f=E(_8e);if(!_8f._){var _8g=_8f.a>>>0;if(!_8g){return -1;}else{var _8h=function(_8i,_8j){while(1){if(_8i>=_8g){if(_8i<=_8g){if(_8i!=_8g){return new F(function(){return _84("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_8j);}}else{return _8j-1|0;}}else{var _8k=imul(_8i,2)>>>0,_8l=_8j+1|0;_8i=_8k;_8j=_8l;continue;}}};return new F(function(){return _8h(1,0);});}}else{return new F(function(){return _86(_8f);});}},_8m=function(_8n){var _8o=E(_8n);if(!_8o._){var _8p=_8o.a>>>0;if(!_8p){return new T2(0,-1,0);}else{var _8q=function(_8r,_8s){while(1){if(_8r>=_8p){if(_8r<=_8p){if(_8r!=_8p){return new F(function(){return _84("GHC/Integer/Type.lhs:(611,5)-(613,40)|function l2");});}else{return E(_8s);}}else{return _8s-1|0;}}else{var _8t=imul(_8r,2)>>>0,_8u=_8s+1|0;_8r=_8t;_8s=_8u;continue;}}};return new T2(0,B(_8q(1,0)),(_8p&_8p-1>>>0)>>>0&4294967295);}}else{var _8v=_8o.a;return new T2(0,B(_8d(_8o)),I_compareInt(I_and(_8v,I_sub(_8v,I_fromInt(1))),0));}},_8w=function(_8x,_8y){var _8z=E(_8x);if(!_8z._){var _8A=_8z.a,_8B=E(_8y);return (_8B._==0)?_8A<=_8B.a:I_compareInt(_8B.a,_8A)>=0;}else{var _8C=_8z.a,_8D=E(_8y);return (_8D._==0)?I_compareInt(_8C,_8D.a)<=0:I_compare(_8C,_8D.a)<=0;}},_8E=function(_8F,_8G){while(1){var _8H=E(_8F);if(!_8H._){var _8I=_8H.a,_8J=E(_8G);if(!_8J._){return new T1(0,(_8I>>>0&_8J.a>>>0)>>>0&4294967295);}else{_8F=new T1(1,I_fromInt(_8I));_8G=_8J;continue;}}else{var _8K=E(_8G);if(!_8K._){_8F=_8H;_8G=new T1(1,I_fromInt(_8K.a));continue;}else{return new T1(1,I_and(_8H.a,_8K.a));}}}},_8L=function(_8M,_8N){while(1){var _8O=E(_8M);if(!_8O._){var _8P=_8O.a,_8Q=E(_8N);if(!_8Q._){var _8R=_8Q.a,_8S=subC(_8P,_8R);if(!E(_8S.b)){return new T1(0,_8S.a);}else{_8M=new T1(1,I_fromInt(_8P));_8N=new T1(1,I_fromInt(_8R));continue;}}else{_8M=new T1(1,I_fromInt(_8P));_8N=_8Q;continue;}}else{var _8T=E(_8N);if(!_8T._){_8M=_8O;_8N=new T1(1,I_fromInt(_8T.a));continue;}else{return new T1(1,I_sub(_8O.a,_8T.a));}}}},_8U=new T1(0,2),_8V=function(_8W,_8X){var _8Y=E(_8W);if(!_8Y._){var _8Z=(_8Y.a>>>0&(2<<_8X>>>0)-1>>>0)>>>0,_90=1<<_8X>>>0;return (_90<=_8Z)?(_90>=_8Z)?1:2:0;}else{var _91=B(_8E(_8Y,B(_8L(B(_6L(_8U,_8X)),_73)))),_92=B(_6L(_73,_8X));return (!B(_6V(_92,_91)))?(!B(_74(_92,_91)))?1:2:0;}},_93=function(_94,_95){while(1){var _96=E(_94);if(!_96._){_94=new T1(1,I_fromInt(_96.a));continue;}else{return new T1(1,I_shiftRight(_96.a,_95));}}},_97=function(_98,_99,_9a,_9b){var _9c=B(_8m(_9b)),_9d=_9c.a;if(!E(_9c.b)){var _9e=B(_8d(_9a));if(_9e<((_9d+_98|0)-1|0)){var _9f=_9d+(_98-_99|0)|0;if(_9f>0){if(_9f>_9e){if(_9f<=(_9e+1|0)){if(!E(B(_8m(_9a)).b)){return 0;}else{return new F(function(){return _6d(_5r,_98-_99|0);});}}else{return 0;}}else{var _9g=B(_93(_9a,_9f));switch(B(_8V(_9a,_9f-1|0))){case 0:return new F(function(){return _6d(_9g,_98-_99|0);});break;case 1:if(!(B(_6p(_9g))&1)){return new F(function(){return _6d(_9g,_98-_99|0);});}else{return new F(function(){return _6d(B(_6s(_9g,_5r)),_98-_99|0);});}break;default:return new F(function(){return _6d(B(_6s(_9g,_5r)),_98-_99|0);});}}}else{return new F(function(){return _6d(_9a,(_98-_99|0)-_9f|0);});}}else{if(_9e>=_99){var _9h=B(_93(_9a,(_9e+1|0)-_99|0));switch(B(_8V(_9a,_9e-_99|0))){case 0:return new F(function(){return _6d(_9h,((_9e-_9d|0)+1|0)-_99|0);});break;case 2:return new F(function(){return _6d(B(_6s(_9h,_5r)),((_9e-_9d|0)+1|0)-_99|0);});break;default:if(!(B(_6p(_9h))&1)){return new F(function(){return _6d(_9h,((_9e-_9d|0)+1|0)-_99|0);});}else{return new F(function(){return _6d(B(_6s(_9h,_5r)),((_9e-_9d|0)+1|0)-_99|0);});}}}else{return new F(function(){return _6d(_9a, -_9d);});}}}else{var _9i=B(_8d(_9a))-_9d|0,_9j=function(_9k){var _9l=function(_9m,_9n){if(!B(_8w(B(_6L(_9n,_99)),_9m))){return new F(function(){return _6P(_9k-_99|0,_9m,_9n);});}else{return new F(function(){return _6P((_9k-_99|0)+1|0,_9m,B(_6L(_9n,1)));});}};if(_9k>=_99){if(_9k!=_99){return new F(function(){return _9l(_9a,new T(function(){return B(_6L(_9b,_9k-_99|0));}));});}else{return new F(function(){return _9l(_9a,_9b);});}}else{return new F(function(){return _9l(new T(function(){return B(_6L(_9a,_99-_9k|0));}),_9b);});}};if(_98>_9i){return new F(function(){return _9j(_98);});}else{return new F(function(){return _9j(_9i);});}}},_9o=new T1(0,2147483647),_9p=new T(function(){return B(_6s(_9o,_73));}),_9q=function(_9r){var _9s=E(_9r);if(!_9s._){var _9t=E(_9s.a);return (_9t==(-2147483648))?E(_9p):new T1(0, -_9t);}else{return new T1(1,I_negate(_9s.a));}},_9u=new T(function(){return 0/0;}),_9v=new T(function(){return -1/0;}),_9w=new T(function(){return 1/0;}),_9x=0,_9y=function(_9z,_9A){if(!B(_6h(_9A,_6K))){if(!B(_6h(_9z,_6K))){if(!B(_74(_9z,_6K))){return new F(function(){return _97(-1021,53,_9z,_9A);});}else{return  -B(_97(-1021,53,B(_9q(_9z)),_9A));}}else{return E(_9x);}}else{return (!B(_6h(_9z,_6K)))?(!B(_74(_9z,_6K)))?E(_9w):E(_9v):E(_9u);}},_9B=function(_9C){var _9D=E(_9C);return new F(function(){return _9y(_9D.a,_9D.b);});},_9E=function(_9F){return 1/E(_9F);},_9G=function(_9H){var _9I=E(_9H);return (_9I!=0)?(_9I<=0)? -_9I:E(_9I):E(_9x);},_9J=function(_9K){var _9L=E(_9K);if(!_9L._){return _9L.a;}else{return new F(function(){return I_toNumber(_9L.a);});}},_9M=function(_9N){return new F(function(){return _9J(_9N);});},_9O=1,_9P=-1,_9Q=function(_9R){var _9S=E(_9R);return (_9S<=0)?(_9S>=0)?E(_9S):E(_9P):E(_9O);},_9T=function(_9U,_9V){return E(_9U)-E(_9V);},_9W=function(_9X){return  -E(_9X);},_9Y=function(_9Z,_a0){return E(_9Z)+E(_a0);},_a1=function(_a2,_a3){return E(_a2)*E(_a3);},_a4={_:0,a:_9Y,b:_9T,c:_a1,d:_9W,e:_9G,f:_9Q,g:_9M},_a5=function(_a6,_a7){return E(_a6)/E(_a7);},_a8=new T4(0,_a4,_a5,_9E,_9B),_a9=function(_aa,_ab){return new T2(1,_aa,new T1(0,_ab));},_ac=function(_ad,_ae,_af){var _ag=E(_ae);if(!_ag._){return new F(function(){return A1(_af,_ag.a);});}else{return new T2(1,_ag.a,new T(function(){return B(_a9(_ag.b,_af));}));}},_ah=function(_ai){return new T1(0,_ai);},_aj=function(_ak){return new F(function(){return err(_ak);});},_al=function(_am){return new T5(0,_am,function(_an,_ai){return new F(function(){return _ac(_am,_an,_ai);});},function(_an,_ai){return new F(function(){return _ao(_am,_an,_ai);});},_ah,_aj);},_ap=function(_aq){return E(E(_aq).b);},_ao=function(_ar,_as,_at){return new F(function(){return A3(_ap,B(_al(_ar)),_as,function(_au){return E(_at);});});},_av=function(_aw){var _ax=new T(function(){return B(_ay(_aw));});return function(_az,_aA){return new F(function(){return _ao(_ax,_az,_aA);});};},_aB=function(_aC,_aD){var _aE=E(_aC);if(!_aE._){var _aF=E(_aD);return (_aF._==0)?E(_aE):new T2(1,_aF.a,new T2(1,_aF.b,new T1(0,function(_aG){return E(_aE);})));}else{var _aH=function(_aI){var _aJ=new T1(0,_aI),_aK=E(_aD);return (_aK._==0)?E(_aJ):new T2(1,_aK.a,new T2(1,_aK.b,new T1(0,function(_aL){return E(_aJ);})));};return new T2(1,_aE.a,new T2(1,_aE.b,new T1(0,_aH)));}},_aM=function(_aN,_aO){var _aP=function(_aQ){var _aR=E(_aO);if(!_aR._){return new T1(0,new T(function(){return B(A1(_aQ,_aR.a));}));}else{var _aS=function(_aT){return new T1(0,new T(function(){return B(A1(_aQ,_aT));}));};return new T2(1,_aR.a,new T2(1,_aR.b,new T1(0,_aS)));}},_aU=E(_aN);if(!_aU._){return new F(function(){return _aP(_aU.a);});}else{return new T2(1,_aU.a,new T2(1,_aU.b,new T1(0,_aP)));}},_ay=function(_aV){return new T5(0,_aV,_ah,_aM,new T(function(){return B(_av(_aV));}),_aB);},_aW=new T(function(){return new T2(0,_aX,_aY);}),_aZ=new T(function(){return B(_ay(_aW));}),_b0=new T(function(){return B(_al(_aZ));}),_b1=function(_b2){return E(E(_b2).d);},_b3=function(_b4,_b5,_b6){var _b7=function(_b8){return new F(function(){return A2(_b1,_b4,new T(function(){return B(A1(_b5,_b8));}));});};return new F(function(){return A3(_ap,_b4,_b6,_b7);});},_aX=function(_an,_ai){return new F(function(){return _b3(_b0,_an,_ai);});},_aY=function(_b9,_ba){return new F(function(){return _aX(function(_bb){return E(_b9);},_ba);});},_bc=function(_bd,_be,_bf){var _bg=E(_bd);return E(_be)*(1-_bg)+E(_bf)*_bg;},_bh=function(_bi,_bj){return (E(_bi)!=E(_bj))?true:false;},_bk=function(_bl,_bm){return E(_bl)==E(_bm);},_bn=new T2(0,_bk,_bh),_bo=function(_bp,_bq){return E(_bp)<E(_bq);},_br=function(_bs,_bt){return E(_bs)<=E(_bt);},_bu=function(_bv,_bw){return E(_bv)>E(_bw);},_bx=function(_by,_bz){return E(_by)>=E(_bz);},_bA=function(_bB,_bC){var _bD=E(_bB),_bE=E(_bC);return (_bD>=_bE)?(_bD!=_bE)?2:1:0;},_bF=function(_bG,_bH){var _bI=E(_bG),_bJ=E(_bH);return (_bI>_bJ)?E(_bI):E(_bJ);},_bK=function(_bL,_bM){var _bN=E(_bL),_bO=E(_bM);return (_bN>_bO)?E(_bO):E(_bN);},_bP={_:0,a:_bn,b:_bA,c:_bo,d:_br,e:_bu,f:_bx,g:_bF,h:_bK},_bQ=function(_bR){var _bS=hs_intToInt64(_bR);return E(_bS);},_bT=function(_bU){var _bV=E(_bU);if(!_bV._){return new F(function(){return _bQ(_bV.a);});}else{return new F(function(){return I_toInt64(_bV.a);});}},_bW=function(_bX){return new F(function(){return _bT(_bX);});},_bY=function(_bZ,_c0){return new F(function(){return hs_timesInt64(E(_bZ),E(_c0));});},_c1=function(_c2,_c3){return new F(function(){return hs_plusInt64(E(_c2),E(_c3));});},_c4=function(_c5,_c6){return new F(function(){return hs_minusInt64(E(_c5),E(_c6));});},_c7=function(_c8){var _c9=hs_geInt64(_c8,new Long(0,0));if(!_c9){var _ca=hs_negateInt64(_c8);return E(_ca);}else{return E(_c8);}},_cb=function(_cc){return new F(function(){return _c7(E(_cc));});},_cd=function(_ce){return new F(function(){return hs_negateInt64(E(_ce));});},_cf=function(_cg){var _ch=hs_gtInt64(_cg,new Long(0,0));if(!_ch){var _ci=hs_eqInt64(_cg,new Long(0,0));if(!_ci){return new F(function(){return new Long(4294967295,-1);});}else{return new F(function(){return new Long(0,0);});}}else{return new F(function(){return new Long(1,0);});}},_cj=function(_ck){return new F(function(){return _cf(E(_ck));});},_cl={_:0,a:_c1,b:_c4,c:_bY,d:_cd,e:_cb,f:_cj,g:_bW},_cm=true,_cn=new T1(0,0),_co=function(_cp,_cq){while(1){var _cr=E(_cp);if(!_cr._){var _cs=_cr.a,_ct=E(_cq);if(!_ct._){return new T1(0,(_cs>>>0|_ct.a>>>0)>>>0&4294967295);}else{_cp=new T1(1,I_fromInt(_cs));_cq=_ct;continue;}}else{var _cu=E(_cq);if(!_cu._){_cp=_cr;_cq=new T1(1,I_fromInt(_cu.a));continue;}else{return new T1(1,I_or(_cr.a,_cu.a));}}}},_cv=function(_cw){var _cx=E(_cw);if(!_cx._){return E(_cn);}else{return new F(function(){return _co(new T1(0,E(_cx.a)),B(_6L(B(_cv(_cx.b)),31)));});}},_cy=function(_cz,_cA){if(!E(_cz)){return new F(function(){return _9q(B(_cv(_cA)));});}else{return new F(function(){return _cv(_cA);});}},_cB=2147483647,_cC=2147483647,_cD=1,_cE=new T2(1,_cD,_6),_cF=new T2(1,_cC,_cE),_cG=new T2(1,_cB,_cF),_cH=new T(function(){return B(_cy(_cm,_cG));}),_cI=0,_cJ=0,_cK=2,_cL=new T2(1,_cK,_6),_cM=new T2(1,_cJ,_cL),_cN=new T2(1,_cI,_cM),_cO=new T(function(){return B(_cy(_5i,_cN));}),_cP=new Long(2,0),_cQ=new T(function(){return B(unCStr("Negative exponent"));}),_cR=new T(function(){return B(err(_cQ));}),_cS=new Long(1,0),_cT=new Long(4294967295,2147483647),_cU=new Long(0,-2147483648),_cV=new T2(0,_cU,_cT),_cW=new T1(0,1),_cX=function(_cY){return E(E(_cY).a);},_cZ=function(_d0){return E(E(_d0).a);},_d1=function(_d2){return E(E(_d2).g);},_d3=function(_d4){return E(E(_d4).b);},_d5=function(_d6){return E(E(_d6).i);},_d7=function(_d8,_d9,_da){var _db=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_d8));})));})));}),_dc=new T(function(){return B(_d3(_d9));}),_dd=function(_de){return (!B(_6V(_de,B(A2(_d5,_d8,_dc)))))?new T2(1,new T(function(){return B(A1(_db,_de));}),new T(function(){return B(_dd(B(_6s(_de,_cW))));})):__Z;};return new F(function(){return _dd(B(A2(_d5,_d8,_da)));});},_df=function(_dg){return new F(function(){return _d7(_dh,_cV,_dg);});},_di=new T1(0,0),_dj=function(_dk,_dl){var _dm=E(_dk);if(!_dm._){var _dn=_dm.a,_do=E(_dl);return (_do._==0)?_dn>=_do.a:I_compareInt(_do.a,_dn)<=0;}else{var _dp=_dm.a,_dq=E(_dl);return (_dq._==0)?I_compareInt(_dp,_dq.a)>=0:I_compare(_dp,_dq.a)>=0;}},_dr=function(_ds,_dt,_du,_dv,_dw){var _dx=function(_dy){if(!B(_6V(_dy,_dw))){return new F(function(){return A2(_ds,_dy,new T(function(){return B(_dx(B(_6s(_dy,_dv))));}));});}else{return E(_dt);}};return new F(function(){return _dx(_du);});},_dz=function(_dA,_dB,_dC,_dD,_dE){if(!B(_dj(_dD,_di))){var _dF=function(_dG){if(!B(_74(_dG,_dE))){return new F(function(){return A2(_dA,_dG,new T(function(){return B(_dF(B(_6s(_dG,_dD))));}));});}else{return E(_dB);}};return new F(function(){return _dF(_dC);});}else{return new F(function(){return _dr(_dA,_dB,_dC,_dD,_dE);});}},_dH=function(_dI){return E(E(_dI).a);},_dJ=function(_dK,_dL,_dM,_dN){var _dO=B(A2(_d5,_dK,_dN)),_dP=B(A2(_d5,_dK,_dM));if(!B(_dj(_dO,_dP))){var _dQ=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_dK));})));})));}),_dR=function(_dS,_dT){return new T2(1,new T(function(){return B(A1(_dQ,_dS));}),_dT);};return new F(function(){return _dz(_dR,_6,_dP,B(_8L(_dO,_dP)),B(A2(_d5,_dK,new T(function(){return B(_dH(_dL));}))));});}else{var _dU=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_dK));})));})));}),_dV=function(_dW,_dX){return new T2(1,new T(function(){return B(A1(_dU,_dW));}),_dX);};return new F(function(){return _dz(_dV,_6,_dP,B(_8L(_dO,_dP)),B(A2(_d5,_dK,new T(function(){return B(_d3(_dL));}))));});}},_dY=function(_dZ,_dg){return new F(function(){return _dJ(_dh,_cV,_dZ,_dg);});},_e0=function(_e1,_e2,_e3,_e4){var _e5=B(A2(_d5,_e1,_e2)),_e6=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_e1));})));})));}),_e7=function(_e8,_e9){return new T2(1,new T(function(){return B(A1(_e6,_e8));}),_e9);};return new F(function(){return _dz(_e7,_6,_e5,B(_8L(B(A2(_d5,_e1,_e3)),_e5)),B(A2(_d5,_e1,_e4)));});},_ea=function(_eb,_dZ,_dg){return new F(function(){return _e0(_dh,_eb,_dZ,_dg);});},_ec=function(_ed,_ee,_ef){var _eg=new T(function(){return B(_d1(new T(function(){return B(_cZ(new T(function(){return B(_cX(_ed));})));})));}),_eh=function(_ei){return (!B(_6V(_ei,B(A2(_d5,_ed,_ef)))))?new T2(1,new T(function(){return B(A1(_eg,_ei));}),new T(function(){return B(_eh(B(_6s(_ei,_cW))));})):__Z;};return new F(function(){return _eh(B(A2(_d5,_ed,_ee)));});},_ej=function(_dZ,_dg){return new F(function(){return _ec(_dh,_dZ,_dg);});},_ek=new T(function(){return hs_intToInt64(2147483647);}),_el=function(_em){return new T1(0,_em);},_en=function(_eo){var _ep=hs_intToInt64(2147483647),_eq=hs_leInt64(_eo,_ep);if(!_eq){return new T1(1,I_fromInt64(_eo));}else{var _er=hs_intToInt64(-2147483648),_es=hs_geInt64(_eo,_er);if(!_es){return new T1(1,I_fromInt64(_eo));}else{var _et=hs_int64ToInt(_eo);return new F(function(){return _el(_et);});}}},_eu=function(_ev){return new F(function(){return _en(E(_ev));});},_ew=function(_ex){while(1){var _ey=E(_ex);if(!_ey._){_ex=new T1(1,I_fromInt(_ey.a));continue;}else{return new F(function(){return I_toString(_ey.a);});}}},_ez=function(_eA,_eB){return new F(function(){return _2(fromJSStr(B(_ew(_eA))),_eB);});},_eC=41,_eD=40,_eE=new T1(0,0),_eF=function(_eG,_eH,_eI){if(_eG<=6){return new F(function(){return _ez(_eH,_eI);});}else{if(!B(_74(_eH,_eE))){return new F(function(){return _ez(_eH,_eI);});}else{return new T2(1,_eD,new T(function(){return B(_2(fromJSStr(B(_ew(_eH))),new T2(1,_eC,_eI)));}));}}},_eJ=function(_eK){return new F(function(){return _eF(0,B(_eu(_eK)),_6);});},_eL=function(_eM,_eN){return new F(function(){return _eF(0,B(_en(E(_eM))),_eN);});},_eO=function(_eP,_eQ){return new F(function(){return _26(_eL,_eP,_eQ);});},_eR=function(_eS,_eT){var _eU=new T(function(){return B(_en(E(_eT)));});return function(_eV){return new F(function(){return _eF(E(_eS),_eU,_eV);});};},_eW=new T3(0,_eR,_eJ,_eO),_eX=new T2(1,_eC,_6),_eY=function(_eZ,_f0,_f1){return new F(function(){return A1(_eZ,new T2(1,_23,new T(function(){return B(A1(_f0,_f1));})));});},_f2=new T(function(){return B(unCStr(": empty list"));}),_f3=new T(function(){return B(unCStr("Prelude."));}),_f4=function(_f5){return new F(function(){return err(B(_2(_f3,new T(function(){return B(_2(_f5,_f2));},1))));});},_f6=new T(function(){return B(unCStr("foldr1"));}),_f7=new T(function(){return B(_f4(_f6));}),_f8=function(_f9,_fa){var _fb=E(_fa);if(!_fb._){return E(_f7);}else{var _fc=_fb.a,_fd=E(_fb.b);if(!_fd._){return E(_fc);}else{return new F(function(){return A2(_f9,_fc,new T(function(){return B(_f8(_f9,_fd));}));});}}},_fe=function(_ff,_fg){var _fh=jsShowI(_ff);return new F(function(){return _2(fromJSStr(_fh),_fg);});},_fi=function(_fj,_fk,_fl){if(_fk>=0){return new F(function(){return _fe(_fk,_fl);});}else{if(_fj<=6){return new F(function(){return _fe(_fk,_fl);});}else{return new T2(1,_eD,new T(function(){var _fm=jsShowI(_fk);return B(_2(fromJSStr(_fm),new T2(1,_eC,_fl)));}));}}},_fn=function(_fo){return new F(function(){return _fi(0,-2147483648,_fo);});},_fp=function(_fq){return new F(function(){return _fi(0,2147483647,_fq);});},_fr=new T2(1,_fp,_6),_fs=new T2(1,_fn,_fr),_ft=new T(function(){return B(_f8(_eY,_fs));}),_fu=new T(function(){return B(A1(_ft,_eX));}),_fv=new T2(1,_eD,_fu),_fw=new T(function(){return B(unAppCStr(") is outside of Int\'s bounds ",_fv));}),_fx=function(_fy){return E(E(_fy).b);},_fz=function(_fA,_fB,_fC){var _fD=new T(function(){var _fE=new T(function(){return B(unAppCStr("}: value (",new T(function(){return B(_2(B(A2(_fx,_fC,_fB)),_fw));})));},1);return B(_2(_fA,_fE));});return new F(function(){return err(B(unAppCStr("Enum.fromEnum{",_fD)));});},_fF=function(_fG,_fH,_fI){return new F(function(){return _fz(_fH,_fI,_fG);});},_fJ=new T(function(){return B(unCStr("Int64"));}),_fK=function(_fL){return new F(function(){return _fF(_eW,_fJ,_fL);});},_fM=function(_fN){return new F(function(){return _fK(_fN);});},_fO=new T(function(){return hs_intToInt64(-2147483648);}),_fP=function(_fQ){var _fR=hs_geInt64(_fQ,E(_fO));if(!_fR){return new F(function(){return _fM(_fQ);});}else{var _fS=hs_leInt64(_fQ,E(_ek));if(!_fS){return new F(function(){return _fM(_fQ);});}else{var _fT=hs_int64ToInt(_fQ);return E(_fT);}}},_fU=function(_fV){return new F(function(){return _fP(E(_fV));});},_fW=new T(function(){return B(unCStr("}: tried to take `pred\' of minBound"));}),_fX=function(_fY){return new F(function(){return err(B(unAppCStr("Enum.pred{",new T(function(){return B(_2(_fY,_fW));}))));});},_fZ=function(_g0){return new F(function(){return _fX(_g0);});},_g1=new T(function(){return B(_fZ(_fJ));}),_g2=function(_g3){var _g4=hs_neInt64(_g3,new Long(0,-2147483648));if(!_g4){return E(_g1);}else{var _g5=hs_minusInt64(_g3,new Long(1,0));return E(_g5);}},_g6=function(_g7){return new F(function(){return _g2(E(_g7));});},_g8=new T(function(){return B(unCStr("}: tried to take `succ\' of maxBound"));}),_g9=function(_ga){return new F(function(){return err(B(unAppCStr("Enum.succ{",new T(function(){return B(_2(_ga,_g8));}))));});},_gb=function(_g0){return new F(function(){return _g9(_g0);});},_gc=new T(function(){return B(_gb(_fJ));}),_gd=function(_ge){var _gf=hs_neInt64(_ge,new Long(4294967295,2147483647));if(!_gf){return E(_gc);}else{var _gg=hs_plusInt64(_ge,new Long(1,0));return E(_gg);}},_gh=function(_gi){return new F(function(){return _gd(E(_gi));});},_gj=function(_gk){return new F(function(){return hs_intToInt64(E(_gk));});},_gl=new T(function(){return {_:0,a:_gh,b:_g6,c:_gj,d:_fU,e:_df,f:_dY,g:_ej,h:_ea};}),_gm=function(_gn,_go){var _gp=hs_minusInt64(_gn,_go);return E(_gp);},_gq=function(_gr,_gs){var _gt=hs_quotInt64(_gr,_gs);return E(_gt);},_gu=function(_gv,_gw){var _gx=hs_intToInt64(1),_gy=_gx,_gz=hs_intToInt64(0),_gA=_gz,_gB=hs_gtInt64(_gv,_gA),_gC=function(_gD){var _gE=hs_ltInt64(_gv,_gA);if(!_gE){return new F(function(){return _gq(_gv,_gw);});}else{var _gF=hs_gtInt64(_gw,_gA);if(!_gF){return new F(function(){return _gq(_gv,_gw);});}else{var _gG=hs_plusInt64(_gv,_gy),_gH=hs_quotInt64(_gG,_gw);return new F(function(){return _gm(_gH,_gy);});}}};if(!_gB){return new F(function(){return _gC(_);});}else{var _gI=hs_ltInt64(_gw,_gA);if(!_gI){return new F(function(){return _gC(_);});}else{var _gJ=hs_minusInt64(_gv,_gy),_gK=hs_quotInt64(_gJ,_gw);return new F(function(){return _gm(_gK,_gy);});}}},_gL=0,_gM=new T(function(){return B(_68(_gL));}),_gN=new T(function(){return die(_gM);}),_gO=function(_gP,_gQ){var _gR=hs_eqInt64(_gQ,new Long(0,0));if(!_gR){var _gS=hs_eqInt64(_gQ,new Long(4294967295,-1));if(!_gS){return new F(function(){return _gu(_gP,_gQ);});}else{var _gT=hs_eqInt64(_gP,new Long(0,-2147483648));if(!_gT){return new F(function(){return _gu(_gP,_gQ);});}else{return E(_gN);}}}else{return E(_6c);}},_gU=function(_gV,_gW){return new F(function(){return _gO(E(_gV),E(_gW));});},_gX=new Long(0,0),_gY=function(_gZ,_h0){var _h1=hs_plusInt64(_gZ,_h0);return E(_h1);},_h2=function(_h3,_h4){var _h5=hs_remInt64(_h3,_h4),_h6=_h5,_h7=hs_intToInt64(0),_h8=_h7,_h9=hs_gtInt64(_h3,_h8),_ha=function(_hb){var _hc=hs_neInt64(_h6,_h8);if(!_hc){return E(_h8);}else{return new F(function(){return _gY(_h6,_h4);});}},_hd=function(_he){var _hf=hs_ltInt64(_h3,_h8);if(!_hf){return E(_h6);}else{var _hg=hs_gtInt64(_h4,_h8);if(!_hg){return E(_h6);}else{return new F(function(){return _ha(_);});}}};if(!_h9){return new F(function(){return _hd(_);});}else{var _hh=hs_ltInt64(_h4,_h8);if(!_hh){return new F(function(){return _hd(_);});}else{return new F(function(){return _ha(_);});}}},_hi=function(_hj,_hk){var _hl=hs_eqInt64(_hk,new Long(0,0));if(!_hl){var _hm=hs_eqInt64(_hk,new Long(4294967295,-1));if(!_hm){return new T2(0,new T(function(){return B(_gu(_hj,_hk));}),new T(function(){return B(_h2(_hj,_hk));}));}else{var _hn=hs_eqInt64(_hj,new Long(0,-2147483648));return (!_hn)?new T2(0,new T(function(){return B(_gu(_hj,_hk));}),new T(function(){return B(_h2(_hj,_hk));})):new T2(0,_gN,_gX);}}else{return E(_6c);}},_ho=function(_hp,_hq){var _hr=B(_hi(E(_hp),E(_hq)));return new T2(0,_hr.a,_hr.b);},_hs=function(_ht,_hu){var _hv=hs_eqInt64(_hu,new Long(0,0));if(!_hv){var _hw=hs_eqInt64(_hu,new Long(4294967295,-1));if(!_hw){return new F(function(){return _h2(_ht,_hu);});}else{return new F(function(){return new Long(0,0);});}}else{return E(_6c);}},_hx=function(_hy,_hz){return new F(function(){return _hs(E(_hy),E(_hz));});},_hA=function(_hB,_hC){var _hD=hs_eqInt64(_hC,new Long(0,0));if(!_hD){var _hE=hs_eqInt64(_hC,new Long(4294967295,-1));if(!_hE){var _hF=hs_quotInt64(_hB,_hC);return E(_hF);}else{var _hG=hs_eqInt64(_hB,new Long(0,-2147483648));if(!_hG){var _hH=hs_quotInt64(_hB,_hC);return E(_hH);}else{return E(_gN);}}}else{return E(_6c);}},_hI=function(_hJ,_hK){return new F(function(){return _hA(E(_hJ),E(_hK));});},_hL=function(_hM,_hN){var _hO=hs_eqInt64(_hN,new Long(0,0));if(!_hO){var _hP=hs_eqInt64(_hN,new Long(4294967295,-1));if(!_hP){return new T2(0,new T(function(){return hs_quotInt64(_hM,_hN);}),new T(function(){return hs_remInt64(_hM,_hN);}));}else{var _hQ=hs_eqInt64(_hM,new Long(0,-2147483648));return (!_hQ)?new T2(0,new T(function(){return hs_quotInt64(_hM,_hN);}),new T(function(){return hs_remInt64(_hM,_hN);})):new T2(0,_gN,_gX);}}else{return E(_6c);}},_hR=function(_hS,_hT){var _hU=B(_hL(E(_hS),E(_hT)));return new T2(0,_hU.a,_hU.b);},_hV=function(_hW,_hX){var _hY=hs_eqInt64(_hX,new Long(0,0));if(!_hY){var _hZ=hs_eqInt64(_hX,new Long(4294967295,-1));if(!_hZ){var _i0=hs_remInt64(_hW,_hX);return E(_i0);}else{return new F(function(){return new Long(0,0);});}}else{return E(_6c);}},_i1=function(_i2,_i3){return new F(function(){return _hV(E(_i2),E(_i3));});},_i4=function(_i5,_i6){return new F(function(){return hs_neInt64(E(_i5),E(_i6));});},_i7=function(_i8,_i9){return new F(function(){return hs_eqInt64(E(_i8),E(_i9));});},_ia=new T2(0,_i7,_i4),_ib=function(_ic,_id){return new F(function(){return hs_ltInt64(E(_ic),E(_id));});},_ie=function(_if,_ig){return new F(function(){return hs_leInt64(E(_if),E(_ig));});},_ih=function(_ii,_ij){return new F(function(){return hs_gtInt64(E(_ii),E(_ij));});},_ik=function(_il,_im){return new F(function(){return hs_geInt64(E(_il),E(_im));});},_in=function(_io,_ip){var _iq=hs_eqInt64(_io,_ip);if(!_iq){var _ir=hs_leInt64(_io,_ip);return (!_ir)?2:0;}else{return 1;}},_is=function(_it,_iu){return new F(function(){return _in(E(_it),E(_iu));});},_iv=function(_iw,_ix){var _iy=E(_iw),_iz=E(_ix),_iA=hs_leInt64(_iy,_iz);return (!_iA)?E(_iy):E(_iz);},_iB=function(_iC,_iD){var _iE=E(_iC),_iF=E(_iD),_iG=hs_leInt64(_iE,_iF);return (!_iG)?E(_iF):E(_iE);},_iH={_:0,a:_ia,b:_is,c:_ib,d:_ie,e:_ih,f:_ik,g:_iv,h:_iB},_iI=new T1(0,1),_iJ=new T1(0,0),_iK=function(_iL,_iM){while(1){var _iN=E(_iL);if(!_iN._){var _iO=E(_iN.a);if(_iO==(-2147483648)){_iL=new T1(1,I_fromInt(-2147483648));continue;}else{var _iP=E(_iM);if(!_iP._){return new T1(0,_iO%_iP.a);}else{_iL=new T1(1,I_fromInt(_iO));_iM=_iP;continue;}}}else{var _iQ=_iN.a,_iR=E(_iM);return (_iR._==0)?new T1(1,I_rem(_iQ,I_fromInt(_iR.a))):new T1(1,I_rem(_iQ,_iR.a));}}},_iS=function(_iT,_iU){if(!B(_6h(_iU,_iJ))){return new F(function(){return _iK(_iT,_iU);});}else{return E(_6c);}},_iV=function(_iW,_iX){while(1){if(!B(_6h(_iX,_iJ))){var _iY=_iX,_iZ=B(_iS(_iW,_iX));_iW=_iY;_iX=_iZ;continue;}else{return E(_iW);}}},_j0=function(_j1){var _j2=E(_j1);if(!_j2._){var _j3=E(_j2.a);return (_j3==(-2147483648))?E(_9p):(_j3<0)?new T1(0, -_j3):E(_j2);}else{var _j4=_j2.a;return (I_compareInt(_j4,0)>=0)?E(_j2):new T1(1,I_negate(_j4));}},_j5=function(_j6,_j7){while(1){var _j8=E(_j6);if(!_j8._){var _j9=E(_j8.a);if(_j9==(-2147483648)){_j6=new T1(1,I_fromInt(-2147483648));continue;}else{var _ja=E(_j7);if(!_ja._){return new T1(0,quot(_j9,_ja.a));}else{_j6=new T1(1,I_fromInt(_j9));_j7=_ja;continue;}}}else{var _jb=_j8.a,_jc=E(_j7);return (_jc._==0)?new T1(0,I_toInt(I_quot(_jb,I_fromInt(_jc.a)))):new T1(1,I_quot(_jb,_jc.a));}}},_jd=5,_je=new T(function(){return B(_68(_jd));}),_jf=new T(function(){return die(_je);}),_jg=function(_jh,_ji){if(!B(_6h(_ji,_iJ))){var _jj=B(_iV(B(_j0(_jh)),B(_j0(_ji))));return (!B(_6h(_jj,_iJ)))?new T2(0,B(_j5(_jh,_jj)),B(_j5(_ji,_jj))):E(_6c);}else{return E(_jf);}},_jk=function(_jl,_jm){while(1){var _jn=E(_jl);if(!_jn._){var _jo=_jn.a,_jp=E(_jm);if(!_jp._){var _jq=_jp.a;if(!(imul(_jo,_jq)|0)){return new T1(0,imul(_jo,_jq)|0);}else{_jl=new T1(1,I_fromInt(_jo));_jm=new T1(1,I_fromInt(_jq));continue;}}else{_jl=new T1(1,I_fromInt(_jo));_jm=_jp;continue;}}else{var _jr=E(_jm);if(!_jr._){_jl=_jn;_jm=new T1(1,I_fromInt(_jr.a));continue;}else{return new T1(1,I_mul(_jn.a,_jr.a));}}}},_js=function(_jt){var _ju=B(_jg(B(_jk(B(_en(E(_jt))),_iI)),_iI));return new T2(0,E(_ju.a),E(_ju.b));},_jv=new T3(0,_cl,_iH,_js),_dh=new T(function(){return {_:0,a:_jv,b:_gl,c:_hI,d:_i1,e:_gU,f:_hx,g:_hR,h:_ho,i:_eu};}),_jw=function(_jx){return E(E(_jx).a);},_jy=function(_jz){return E(E(_jz).b);},_jA=function(_jB){return E(E(_jB).a);},_jC=new T1(0,2),_jD=function(_jE){return E(E(_jE).d);},_jF=function(_jG,_jH){var _jI=B(_cX(_jG)),_jJ=new T(function(){return B(_cZ(_jI));}),_jK=new T(function(){return B(A3(_jD,_jG,_jH,new T(function(){return B(A2(_d1,_jJ,_jC));})));});return new F(function(){return A3(_jA,B(_jw(B(_jy(_jI)))),_jK,new T(function(){return B(A2(_d1,_jJ,_iJ));}));});},_jL=function(_jM,_jN,_jO){while(1){var _jP=B((function(_jQ,_jR,_jS){if(!B(_jF(_dh,_jR))){var _jT=hs_eqInt64(_jR,new Long(1,0));if(!_jT){var _jU=hs_minusInt64(_jR,new Long(1,0));_jM=new T(function(){return B(_bY(_jQ,_jQ));});_jN=B(_hA(_jU,new Long(2,0)));_jO=new T(function(){return B(_bY(_jQ,_jS));},1);return __continue;}else{var _jV=hs_timesInt64(E(_jQ),E(_jS));return E(_jV);}}else{var _jW=B(_hA(_jR,new Long(2,0))),_jX=_jS;_jM=new T(function(){return B(_bY(_jQ,_jQ));});_jN=_jW;_jO=_jX;return __continue;}})(_jM,_jN,_jO));if(_jP!=__continue){return _jP;}}},_jY=function(_jZ,_k0){while(1){var _k1=B((function(_k2,_k3){if(!B(_jF(_dh,_k3))){var _k4=hs_eqInt64(_k3,new Long(1,0));if(!_k4){var _k5=hs_minusInt64(_k3,new Long(1,0));return new F(function(){return _jL(new T(function(){return B(_bY(_k2,_k2));}),B(_hA(_k5,new Long(2,0))),_k2);});}else{return E(_k2);}}else{var _k6=B(_hA(_k3,new Long(2,0)));_jZ=new T(function(){return B(_bY(_k2,_k2));});_k0=_k6;return __continue;}})(_jZ,_k0));if(_k1!=__continue){return _k1;}}},_k7=function(_k8,_k9){var _ka=hs_ltInt64(_k9,new Long(0,0));if(!_ka){var _kb=hs_eqInt64(_k9,new Long(0,0));if(!_kb){return new F(function(){return _jY(_k8,_k9);});}else{return E(_cS);}}else{return E(_cR);}},_kc=new T(function(){return B(_k7(_cP,new Long(53,0)));}),_kd=new T(function(){return B(_9J(B(_en(E(_kc)))));}),_ke=new T(function(){return hs_minusInt64(E(_kc),new Long(1,0));}),_kf=function(_kg,_kh){var _ki=hs_int64ToWord64(_kh),_kj=hs_int64ToWord64(_kg),_kk=hs_and64(_kj,_ki),_kl=hs_word64ToInt64(_kk);return E(_kl);},_km=new T1(0,1),_kn=function(_ko,_kp){return new T2(0,E(_ko),E(_kp));},_kq=function(_kr,_ks){var _kt=quot(_ks,52774),_ku=(imul(40692,_ks-(imul(_kt,52774)|0)|0)|0)-(imul(_kt,3791)|0)|0,_kv=new T(function(){if(_ku>=0){return _ku;}else{return _ku+2147483399|0;}}),_kw=quot(_kr,53668),_kx=(imul(40014,_kr-(imul(_kw,53668)|0)|0)|0)-(imul(_kw,12211)|0)|0,_ky=new T(function(){if(_kx>=0){return _kx;}else{return _kx+2147483563|0;}});return new T2(0,new T(function(){var _kz=E(_ky)-E(_kv)|0;if(_kz>=1){return _kz;}else{return _kz+2147483562|0;}}),new T(function(){return B(_kn(_ky,_kv));}));},_kA=new T1(0,2147483562),_kB=new T1(0,0),_kC=new T1(0,1000),_kD=function(_kE,_kF){var _kG=_kE%_kF;if(_kE<=0){if(_kE>=0){return E(_kG);}else{if(_kF<=0){return E(_kG);}else{var _kH=E(_kG);return (_kH==0)?0:_kH+_kF|0;}}}else{if(_kF>=0){if(_kE>=0){return E(_kG);}else{if(_kF<=0){return E(_kG);}else{var _kI=E(_kG);return (_kI==0)?0:_kI+_kF|0;}}}else{var _kJ=E(_kG);return (_kJ==0)?0:_kJ+_kF|0;}}},_kK=function(_kL,_kM){while(1){var _kN=E(_kL);if(!_kN._){var _kO=E(_kN.a);if(_kO==(-2147483648)){_kL=new T1(1,I_fromInt(-2147483648));continue;}else{var _kP=E(_kM);if(!_kP._){return new T1(0,B(_kD(_kO,_kP.a)));}else{_kL=new T1(1,I_fromInt(_kO));_kM=_kP;continue;}}}else{var _kQ=_kN.a,_kR=E(_kM);return (_kR._==0)?new T1(1,I_mod(_kQ,I_fromInt(_kR.a))):new T1(1,I_mod(_kQ,_kR.a));}}},_kS=function(_kT,_kU,_kV,_kW){while(1){var _kX=B((function(_kY,_kZ,_l0,_l1){if(!B(_6V(_kZ,_l0))){var _l2=B(_6s(B(_8L(_l0,_kZ)),_km)),_l3=function(_l4,_l5,_l6){while(1){if(!B(_dj(_l4,B(_jk(_l2,_kC))))){var _l7=E(_l6),_l8=B(_kq(_l7.a,_l7.b)),_l9=B(_jk(_l4,_kA)),_la=B(_6s(B(_jk(_l5,_kA)),B(_8L(B(_el(E(_l8.a))),_km))));_l4=_l9;_l5=_la;_l6=_l8.b;continue;}else{return new T2(0,_l5,_l6);}}},_lb=B(_l3(_km,_kB,_l1)),_lc=new T(function(){return B(A2(_d1,_kY,new T(function(){if(!B(_6h(_l2,_kB))){return B(_6s(_kZ,B(_kK(_lb.a,_l2))));}else{return E(_6c);}})));});return new T2(0,_lc,_lb.b);}else{var _ld=_kY,_le=_l0,_lf=_kZ,_lg=_l1;_kT=_ld;_kU=_le;_kV=_lf;_kW=_lg;return __continue;}})(_kT,_kU,_kV,_kW));if(_kX!=__continue){return _kX;}}},_lh=function(_li){var _lj=B(_kS(_cl,_cO,_cH,_li));return new T2(0,new T(function(){return B(_9J(B(_en(B(_kf(E(_ke),E(_lj.a)))))))/E(_kd);}),_lj.b);},_lk=function(_ll,_lm,_ln){while(1){var _lo=B((function(_lp,_lq,_lr){if(_lp<=_lq){var _ls=new T(function(){var _lt=B(_lh(_lr));return new T2(0,_lt.a,_lt.b);});return new T2(0,new T(function(){var _lu=E(E(_ls).a);return 0.5*_lp+_lu*(0.5*_lq-0.5*_lp)+0.5*_lp+_lu*(0.5*_lq-0.5*_lp);}),new T(function(){return E(E(_ls).b);}));}else{var _lv=_lq,_lw=_lp,_lx=_lr;_ll=_lv;_lm=_lw;_ln=_lx;return __continue;}})(_ll,_lm,_ln));if(_lo!=__continue){return _lo;}}},_ly=1420103680,_lz=465,_lA=new T2(1,_lz,_6),_lB=new T2(1,_ly,_lA),_lC=new T(function(){return B(_cy(_cm,_lB));}),_lD=0,_lE=function(_lF,_lG){var _lH=E(_lG);if(!_lH){return E(_6c);}else{var _lI=function(_lJ){if(_lF<=0){if(_lF>=0){var _lK=quotRemI(_lF,_lH);return new T2(0,_lK.a,_lK.b);}else{if(_lH<=0){var _lL=quotRemI(_lF,_lH);return new T2(0,_lL.a,_lL.b);}else{var _lM=quotRemI(_lF+1|0,_lH);return new T2(0,_lM.a-1|0,(_lM.b+_lH|0)-1|0);}}}else{if(_lH>=0){if(_lF>=0){var _lN=quotRemI(_lF,_lH);return new T2(0,_lN.a,_lN.b);}else{if(_lH<=0){var _lO=quotRemI(_lF,_lH);return new T2(0,_lO.a,_lO.b);}else{var _lP=quotRemI(_lF+1|0,_lH);return new T2(0,_lP.a-1|0,(_lP.b+_lH|0)-1|0);}}}else{var _lQ=quotRemI(_lF-1|0,_lH);return new T2(0,_lQ.a-1|0,(_lQ.b+_lH|0)+1|0);}}};if(E(_lH)==(-1)){if(E(_lF)==(-2147483648)){return new T2(0,_gN,_lD);}else{return new F(function(){return _lI(_);});}}else{return new F(function(){return _lI(_);});}}},_lR=new T1(0,-1),_lS=function(_lT){var _lU=E(_lT);if(!_lU._){var _lV=_lU.a;return (_lV>=0)?(E(_lV)==0)?E(_cn):E(_73):E(_lR);}else{var _lW=I_compareInt(_lU.a,0);return (_lW<=0)?(E(_lW)==0)?E(_cn):E(_lR):E(_73);}},_lX=function(_lY,_lZ,_m0,_m1){var _m2=B(_jk(_lZ,_m0));return new F(function(){return _jg(B(_jk(B(_jk(_lY,_m1)),B(_lS(_m2)))),B(_j0(_m2)));});},_m3=function(_m4){return E(_lC);},_m5=new T1(0,1),_m6=function(_m7,_m8){var _m9=E(_m7);return new T2(0,_m9,new T(function(){var _ma=B(_m6(B(_6s(_m9,_m8)),_m8));return new T2(1,_ma.a,_ma.b);}));},_mb=function(_mc){var _md=B(_m6(_mc,_m5));return new T2(1,_md.a,_md.b);},_me=function(_mf,_mg){var _mh=B(_m6(_mf,new T(function(){return B(_8L(_mg,_mf));})));return new T2(1,_mh.a,_mh.b);},_mi=function(_mj,_mk,_ml){if(!B(_dj(_mk,_di))){var _mm=function(_mn){return (!B(_74(_mn,_ml)))?new T2(1,_mn,new T(function(){return B(_mm(B(_6s(_mn,_mk))));})):__Z;};return new F(function(){return _mm(_mj);});}else{var _mo=function(_mp){return (!B(_6V(_mp,_ml)))?new T2(1,_mp,new T(function(){return B(_mo(B(_6s(_mp,_mk))));})):__Z;};return new F(function(){return _mo(_mj);});}},_mq=function(_mr,_ms,_mt){return new F(function(){return _mi(_mr,B(_8L(_ms,_mr)),_mt);});},_mu=function(_mv,_mw){return new F(function(){return _mi(_mv,_m5,_mw);});},_mx=function(_my){return new F(function(){return _6p(_my);});},_mz=function(_mA){return new F(function(){return _8L(_mA,_m5);});},_mB=function(_mC){return new F(function(){return _6s(_mC,_m5);});},_mD=function(_mE){return new F(function(){return _el(E(_mE));});},_mF={_:0,a:_mB,b:_mz,c:_mD,d:_mx,e:_mb,f:_me,g:_mu,h:_mq},_mG=function(_mH,_mI){if(_mH<=0){if(_mH>=0){return new F(function(){return quot(_mH,_mI);});}else{if(_mI<=0){return new F(function(){return quot(_mH,_mI);});}else{return quot(_mH+1|0,_mI)-1|0;}}}else{if(_mI>=0){if(_mH>=0){return new F(function(){return quot(_mH,_mI);});}else{if(_mI<=0){return new F(function(){return quot(_mH,_mI);});}else{return quot(_mH+1|0,_mI)-1|0;}}}else{return quot(_mH-1|0,_mI)-1|0;}}},_mJ=function(_mK,_mL){while(1){var _mM=E(_mK);if(!_mM._){var _mN=E(_mM.a);if(_mN==(-2147483648)){_mK=new T1(1,I_fromInt(-2147483648));continue;}else{var _mO=E(_mL);if(!_mO._){return new T1(0,B(_mG(_mN,_mO.a)));}else{_mK=new T1(1,I_fromInt(_mN));_mL=_mO;continue;}}}else{var _mP=_mM.a,_mQ=E(_mL);return (_mQ._==0)?new T1(1,I_div(_mP,I_fromInt(_mQ.a))):new T1(1,I_div(_mP,_mQ.a));}}},_mR=function(_mS,_mT){if(!B(_6h(_mT,_iJ))){return new F(function(){return _mJ(_mS,_mT);});}else{return E(_6c);}},_mU=function(_mV,_mW){while(1){var _mX=E(_mV);if(!_mX._){var _mY=E(_mX.a);if(_mY==(-2147483648)){_mV=new T1(1,I_fromInt(-2147483648));continue;}else{var _mZ=E(_mW);if(!_mZ._){var _n0=_mZ.a;return new T2(0,new T1(0,B(_mG(_mY,_n0))),new T1(0,B(_kD(_mY,_n0))));}else{_mV=new T1(1,I_fromInt(_mY));_mW=_mZ;continue;}}}else{var _n1=E(_mW);if(!_n1._){_mV=_mX;_mW=new T1(1,I_fromInt(_n1.a));continue;}else{var _n2=I_divMod(_mX.a,_n1.a);return new T2(0,new T1(1,_n2.a),new T1(1,_n2.b));}}}},_n3=function(_n4,_n5){if(!B(_6h(_n5,_iJ))){var _n6=B(_mU(_n4,_n5));return new T2(0,_n6.a,_n6.b);}else{return E(_6c);}},_n7=function(_n8,_n9){if(!B(_6h(_n9,_iJ))){return new F(function(){return _kK(_n8,_n9);});}else{return E(_6c);}},_na=function(_nb,_nc){if(!B(_6h(_nc,_iJ))){return new F(function(){return _j5(_nb,_nc);});}else{return E(_6c);}},_nd=function(_ne,_nf){if(!B(_6h(_nf,_iJ))){var _ng=B(_6B(_ne,_nf));return new T2(0,_ng.a,_ng.b);}else{return E(_6c);}},_nh=function(_ni){return E(_ni);},_nj=function(_nk){return E(_nk);},_nl={_:0,a:_6s,b:_8L,c:_jk,d:_9q,e:_j0,f:_lS,g:_nj},_nm=function(_nn,_no){var _np=E(_nn);if(!_np._){var _nq=_np.a,_nr=E(_no);return (_nr._==0)?_nq!=_nr.a:(I_compareInt(_nr.a,_nq)==0)?false:true;}else{var _ns=_np.a,_nt=E(_no);return (_nt._==0)?(I_compareInt(_ns,_nt.a)==0)?false:true:(I_compare(_ns,_nt.a)==0)?false:true;}},_nu=new T2(0,_6h,_nm),_nv=function(_nw,_nx){return (!B(_8w(_nw,_nx)))?E(_nw):E(_nx);},_ny=function(_nz,_nA){return (!B(_8w(_nz,_nA)))?E(_nA):E(_nz);},_nB={_:0,a:_nu,b:_5s,c:_74,d:_8w,e:_6V,f:_dj,g:_nv,h:_ny},_nC=function(_nD){return new T2(0,E(_nD),E(_cW));},_nE=new T3(0,_nl,_nB,_nC),_nF={_:0,a:_nE,b:_mF,c:_na,d:_iS,e:_mR,f:_n7,g:_nd,h:_n3,i:_nh},_nG=new T1(0,0),_nH=function(_nI,_nJ,_nK){var _nL=B(A1(_nI,_nJ));if(!B(_6h(_nL,_nG))){return new F(function(){return _mJ(B(_jk(_nJ,_nK)),_nL);});}else{return E(_6c);}},_nM=function(_nN,_nO,_nP){var _nQ=new T(function(){if(!B(_6h(_nP,_iJ))){var _nR=B(_6B(_nO,_nP));return new T2(0,_nR.a,_nR.b);}else{return E(_6c);}}),_nS=new T(function(){return B(A2(_d1,B(_cZ(B(_cX(_nN)))),new T(function(){return E(E(_nQ).a);})));});return new T2(0,_nS,new T(function(){return new T2(0,E(E(_nQ).b),E(_nP));}));},_nT=function(_nU){return E(E(_nU).b);},_nV=function(_nW,_nX,_nY){var _nZ=B(_nM(_nW,_nX,_nY)),_o0=_nZ.a,_o1=E(_nZ.b);if(!B(_74(B(_jk(_o1.a,_cW)),B(_jk(_iJ,_o1.b))))){return E(_o0);}else{var _o2=B(_cZ(B(_cX(_nW))));return new F(function(){return A3(_nT,_o2,_o0,new T(function(){return B(A2(_d1,_o2,_cW));}));});}},_o3=479723520,_o4=40233135,_o5=new T2(1,_o4,_6),_o6=new T2(1,_o3,_o5),_o7=new T(function(){return B(_cy(_cm,_o6));}),_o8=new T1(0,40587),_o9=function(_oa){var _ob=new T(function(){var _oc=B(_lX(_oa,_cW,_lC,_cW)),_od=B(_lX(_o7,_cW,_lC,_cW)),_oe=B(_lX(_oc.a,_oc.b,_od.a,_od.b));return B(_nV(_nF,_oe.a,_oe.b));});return new T2(0,new T(function(){return B(_6s(_o8,_ob));}),new T(function(){return B(_8L(_oa,B(_nH(_m3,B(_jk(_ob,_lC)),_o7))));}));},_of=new T1(0,0),_og=function(_oh,_){var _oi=__get(_oh,0),_oj=__get(_oh,1),_ok=Number(_oi),_ol=jsTrunc(_ok),_om=Number(_oj),_on=jsTrunc(_om);return new T2(0,_ol,_on);},_oo=new T(function(){return eval("(function(){var ms = new Date().getTime();                   return [(ms/1000)|0, ((ms % 1000)*1000)|0];})");}),_op=660865024,_oq=465661287,_or=new T2(1,_oq,_6),_os=new T2(1,_op,_or),_ot=new T(function(){return B(_cy(_cm,_os));}),_ou=function(_){var _ov=__app0(E(_oo)),_ow=B(_og(_ov,_));return new T(function(){var _ox=E(_ow);if(!B(_6h(_ot,_nG))){return B(_6s(B(_jk(B(_el(E(_ox.a))),_lC)),B(_mJ(B(_jk(B(_jk(B(_el(E(_ox.b))),_lC)),_lC)),_ot))));}else{return E(_6c);}});},_oy=new T1(0,12345),_oz=function(_){var _oA=B(_ou(0)),_oB=B(_lX(B(_o9(_oA)).b,_cW,_lC,_cW)),_oC=_oB.b;if(!B(_6h(_oC,_kB))){var _oD=B(_6B(_oB.a,_oC));return new F(function(){return nMV(new T(function(){var _oE=B(_lE((B(_6p(B(_6s(B(_6s(B(_6s(B(_jk(_oD.a,_oy)),_oD.b)),_of)),_kB))))>>>0&2147483647)>>>0&4294967295,2147483562));return new T2(0,E(_oE.b)+1|0,B(_kD(E(_oE.a),2147483398))+1|0);}));});}else{return E(_6c);}},_oF=new T(function(){return B(_4n(_oz));}),_oG=function(_oH,_){var _oI=mMV(E(_oF),function(_oJ){var _oK=E(_oH),_oL=B(_lk(E(_oK.a),E(_oK.b),_oJ));return new T2(0,E(_oL.b),_oL.a);}),_oM=E(_oI);return _oI;},_oN=new T1(0,_7),_oO=new T(function(){return B(unCStr("!!: negative index"));}),_oP=new T(function(){return B(_2(_f3,_oO));}),_oQ=new T(function(){return B(err(_oP));}),_oR=new T(function(){return B(unCStr("!!: index too large"));}),_oS=new T(function(){return B(_2(_f3,_oR));}),_oT=new T(function(){return B(err(_oS));}),_oU=function(_oV,_oW){while(1){var _oX=E(_oV);if(!_oX._){return E(_oT);}else{var _oY=E(_oW);if(!_oY){return E(_oX.a);}else{_oV=_oX.b;_oW=_oY-1|0;continue;}}}},_oZ=function(_p0,_p1){if(_p1>=0){return new F(function(){return _oU(_p0,_p1);});}else{return E(_oQ);}},_p2=new T2(0,_2G,_C),_p3=new T0(2),_p4=function(_p5){return new T0(2);},_p6=function(_p7,_p8,_p9){return function(_){var _pa=E(_p7),_pb=rMV(_pa),_pc=E(_pb);if(!_pc._){var _pd=new T(function(){var _pe=new T(function(){return B(A1(_p9,_7));});return B(_2(_pc.b,new T2(1,new T2(0,_p8,function(_pf){return E(_pe);}),_6)));}),_=wMV(_pa,new T2(0,_pc.a,_pd));return _p3;}else{var _pg=E(_pc.a);if(!_pg._){var _=wMV(_pa,new T2(0,_p8,_6));return new T(function(){return B(A1(_p9,_7));});}else{var _=wMV(_pa,new T1(1,_pg.b));return new T1(1,new T2(1,new T(function(){return B(A1(_p9,_7));}),new T2(1,new T(function(){return B(A2(_pg.a,_p8,_p4));}),_6)));}}};},_ph=new T1(1,_6),_pi=function(_pj,_pk){return function(_){var _pl=E(_pj),_pm=rMV(_pl),_pn=E(_pm);if(!_pn._){var _po=_pn.a,_pp=E(_pn.b);if(!_pp._){var _=wMV(_pl,_ph);return new T(function(){return B(A1(_pk,_po));});}else{var _pq=E(_pp.a),_=wMV(_pl,new T2(0,_pq.a,_pp.b));return new T1(1,new T2(1,new T(function(){return B(A1(_pk,_po));}),new T2(1,new T(function(){return B(A1(_pq.b,_p4));}),_6)));}}else{var _pr=new T(function(){var _ps=function(_pt){var _pu=new T(function(){return B(A1(_pk,_pt));});return function(_pv){return E(_pu);};};return B(_2(_pn.a,new T2(1,_ps,_6)));}),_=wMV(_pl,new T1(1,_pr));return _p3;}};},_pw=function(_px){return E(E(_px).a);},_py=function(_pz){return E(E(_pz).a);},_pA=new T(function(){return eval("(function(t,f){window.setInterval(f,t);})");}),_pB=new T(function(){return eval("(function(t,f){window.setTimeout(f,t);})");}),_pC=function(_pD){return E(E(_pD).b);},_pE=function(_pF){return E(E(_pF).b);},_pG=function(_pH,_pI,_pJ){var _pK=B(_pw(_pH)),_pL=new T(function(){return B(_pC(_pK));}),_pM=function(_pN){var _pO=function(_){var _pP=E(_pI);if(!_pP._){var _pQ=B(A1(_pN,_7)),_pR=__createJSFunc(0,function(_){var _pS=B(A1(_pQ,_));return _4r;}),_pT=__app2(E(_pB),_pP.a,_pR);return new T(function(){var _pU=Number(_pT),_pV=jsTrunc(_pU);return new T2(0,_pV,E(_pP));});}else{var _pW=B(A1(_pN,_7)),_pX=__createJSFunc(0,function(_){var _pY=B(A1(_pW,_));return _4r;}),_pZ=__app2(E(_pA),_pP.a,_pX);return new T(function(){var _q0=Number(_pZ),_q1=jsTrunc(_q0);return new T2(0,_q1,E(_pP));});}};return new F(function(){return A1(_pL,_pO);});},_q2=new T(function(){return B(A2(_pE,_pH,function(_q3){return E(_pJ);}));});return new F(function(){return A3(_ap,B(_py(_pK)),_q2,_pM);});},_q4=new T1(1,_6),_q5=function(_q6,_q7){return function(_){var _q8=nMV(_q4),_q9=_q8,_qa=function(_){var _qb=function(_){return new F(function(){return _e(new T(function(){return new T1(0,B(_p6(_q9,_7,_p4)));}),_6,_);});},_qc=B(A(_pG,[_p2,new T(function(){return new T1(0,E(_q6));}),_qb,_]));return new T(function(){return new T1(0,B(_pi(_q9,_q7)));});};return new T1(0,_qa);};},_qd=0,_qe=new T1(1,_6),_qf=function(_qg,_qh,_qi){return function(_){var _qj=nMV(_qe),_qk=_qj;return new T(function(){var _ql=function(_qm){var _qn=new T(function(){return B(A1(_qi,new T2(0,_7,E(_qm).b)));}),_qo=function(_qp){return E(_qn);};return new T1(0,B(_pi(_qk,function(_qq){return new T1(0,B(_q5(_qd,_qo)));})));},_qr=function(_qs,_qt){return new T1(0,B(_p6(_qk,_7,function(_qu){return new F(function(){return A1(_qt,new T2(0,_qu,_qs));});})));};return B(A3(_qg,_qr,_qh,_ql));});};},_qv=function(_qw){return E(E(_qw).a);},_qx=function(_qy,_qz,_qA,_qB,_){var _qC=E(_qy);switch(_qC._){case 0:return new F(function(){return A(_qz,[_qC.a,_qA,_qB,_]);});break;case 1:var _qD=B(A1(_qC.a,_));return new F(function(){return A(_qz,[_qD,_qA,_qB,_]);});break;case 2:var _qE=rMV(E(E(_qC.a).c)),_qF=E(_qE);if(!_qF._){var _qG=new T(function(){return B(A1(_qC.b,new T(function(){return B(_qv(_qF.a));})));});return new F(function(){return A(_qz,[_qG,_qA,_qB,_]);});}else{return _7;}break;default:var _qH=rMV(E(E(_qC.a).c)),_qI=E(_qH);if(!_qI._){var _qJ=B(A2(_qC.b,E(_qI.a).a,_));return new F(function(){return A(_qz,[_qJ,_qA,_qB,_]);});}else{return _7;}}},_qK=function(_qL,_qM,_){var _qN=E(_qL);switch(_qN._){case 0:return new F(function(){return A2(_qM,_qN.a,_);});break;case 1:var _qO=B(A1(_qN.a,_));return new F(function(){return A2(_qM,_qO,_);});break;case 2:var _qP=rMV(E(E(_qN.a).c)),_qQ=E(_qP);if(!_qQ._){var _qR=new T(function(){return B(A1(_qN.b,new T(function(){return B(_qv(_qQ.a));})));});return new F(function(){return A2(_qM,_qR,_);});}else{return _5i;}break;default:var _qS=rMV(E(E(_qN.a).c)),_qT=E(_qS);if(!_qT._){var _qU=B(A2(_qN.b,E(_qT.a).a,_));return new F(function(){return A2(_qM,_qU,_);});}else{return _5i;}}},_qV=function(_){return _7;},_qW=new T(function(){return eval("(function(x1,y1,x2,y2,x,y,ctx,_){ctx.bezierCurveTo(x1,y1,x2,y2,x,y);})");}),_qX=new T(function(){return eval("(function(x,y,ctx,_){ctx.moveTo(x,y);})");}),_qY=new T(function(){return 4*(Math.sqrt(2)-1)/3;}),_qZ=function(_r0,_r1,_r2){var _r3=function(_r4,_r5,_r6,_){var _r7=function(_r8,_r9,_ra,_){return new F(function(){return _qx(_r2,function(_rb,_rc,_rd,_){var _re=E(_r4),_rf=E(_r8),_rg=E(_rb),_rh=E(_rc),_ri=_rf-_rg,_rj=E(_rd),_rk=__app4(E(_qX),_re,_ri,_rh,_rj),_rl=E(_qY),_rm=E(_qW),_rn=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_rf,new T2(1,_re+_rg,new T2(1,_rf-_rg*_rl,new T2(1,_re+_rg,new T2(1,_ri,new T2(1,_re+_rg*_rl,_6))))))))),_ro=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_rf+_rg,new T2(1,_re,new T2(1,_rf+_rg,new T2(1,_re+_rg*_rl,new T2(1,_rf+_rg*_rl,new T2(1,_re+_rg,_6))))))))),_rp=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_rf,new T2(1,_re-_rg,new T2(1,_rf+_rg*_rl,new T2(1,_re-_rg,new T2(1,_rf+_rg,new T2(1,_re-_rg*_rl,_6))))))))),_rq=__apply(_rm,new T2(1,_rj,new T2(1,_rh,new T2(1,_ri,new T2(1,_re,new T2(1,_ri,new T2(1,_re-_rg*_rl,new T2(1,_rf-_rg*_rl,new T2(1,_re-_rg,_6)))))))));return new F(function(){return _qV(_);});},_r9,_ra,_);});};return new F(function(){return _qx(_r1,_r7,_r5,_r6,_);});},_rr=function(_rs,_){var _rt=E(_rs),_ru=function(_rv,_){var _rw=function(_rx,_){var _ry=function(_rz,_){return new T(function(){var _rA=E(_rz),_rB=E(_rx)-E(_rt.b),_rC=E(_rv)-E(_rt.a);return _rC*_rC+_rB*_rB<=_rA*_rA;});};return new F(function(){return _qK(_r2,_ry,_);});};return new F(function(){return _qK(_r1,_rw,_);});};return new F(function(){return _qK(_r0,_ru,_);});};return new T3(0,_rr,function(_rD,_rE,_){return new F(function(){return _qx(_r0,_r3,_rD,_rE,_);});},_7);},_rF=function(_rG){return E(E(_rG).a);},_rH=function(_rI){return E(E(_rI).c);},_rJ=function(_rK){return E(E(_rK).b);},_rL=function(_rM,_rN,_rO){return new T1(0,B(_p6(_rM,_rN,_rO)));},_rP=function(_rQ,_rR){return new T1(0,B(_pi(_rQ,_rR)));},_rS=function(_rT,_rU,_rV){var _rW=new T(function(){return B(_rJ(_rT));}),_rX=B(_rF(_rT)),_rY=function(_rZ,_s0){var _s1=new T(function(){return B(A1(_rW,function(_s2){return new F(function(){return _rL(_rU,_s0,_s2);});}));});return new F(function(){return A3(_rH,_rX,_s1,new T(function(){return B(A2(_b1,_rX,_rZ));}));});},_s3=function(_s4){var _s5=E(_s4);return new F(function(){return _rY(_s5.a,_s5.b);});},_s6=function(_s7){return new F(function(){return A3(_ap,_rX,new T(function(){return B(A1(_rV,_s7));}),_s3);});},_s8=new T(function(){return B(A2(_rJ,_rT,function(_s2){return new F(function(){return _rP(_rU,_s2);});}));});return new F(function(){return A3(_ap,_rX,_s8,_s6);});},_s9=function(_sa,_sb,_sc){var _sd=new T(function(){return E(E(_sa).b);});return new F(function(){return A1(_sc,new T2(0,new T2(0,_7,new T2(0,new T(function(){return E(E(_sa).a);}),new T4(0,new T(function(){return E(E(_sd).a);}),new T(function(){return E(E(_sd).b);}),new T(function(){return E(E(_sd).c);}),_5i))),_sb));});},_se=0,_sf=function(_sg,_sh,_si,_sj){var _sk=function(_sl,_sm,_sn){return new F(function(){return A1(_sn,new T2(0,new T2(0,_7,new T(function(){var _so=E(_sl);return new T4(0,E(new T2(1,new T2(0,_sg,_sh),_so.a)),_so.b,E(_so.c),E(_so.d));})),_sm));});};return new F(function(){return A(_rS,[_4l,_si,_sk,_si,_sj]);});},_sp=function(_sq,_sr,_ss,_st,_su,_sv){var _sw=new T(function(){var _sx=new T(function(){return B(A1(_ss,_2E));}),_sy=function(_sz,_sA,_sB){var _sC=E(_sz),_sD=E(_sC.b),_sE=new T(function(){var _sF=new T(function(){return B(A1(_sx,new T(function(){return B(_a5(_sD.c,_sr));})));});return B(A3(_sq,_sF,_sD.a,_sD.b));});return new F(function(){return A1(_sB,new T2(0,new T2(0,_7,new T2(0,_sC.a,new T4(0,_sE,_su,_se,_sD.d))),_sA));});};return B(_rS(_4l,_st,_sy));}),_sG=new T(function(){return B(_rS(_4l,_st,_s9));}),_sH=new T(function(){var _sI=new T(function(){return B(A1(_sv,_5i));}),_sJ=new T(function(){return B(A1(_sv,_cm));}),_sK=new T(function(){return B(A1(_ss,_2E));}),_sL=function(_sM,_sN,_sO){var _sP=E(_sM),_sQ=E(_sP.b),_sR=_sQ.a,_sS=_sQ.b;if(!E(_sQ.d)){var _sT=E(_sr),_sU=E(_sQ.c)+1,_sV=function(_sW,_sX){var _sY=new T(function(){var _sZ=new T(function(){return B(A1(_sK,new T(function(){return _sW/_sT;})));});return B(A3(_sq,_sZ,_sR,_sS));}),_t0=new T4(0,_sR,_sS,_sX,_cm);if(_sW>=_sT){return new F(function(){return A2(_sJ,_sN,function(_t1){return new F(function(){return A1(_sO,new T2(0,new T2(0,_5i,new T2(0,_sY,_t0)),E(_t1).b));});});});}else{return new F(function(){return A1(_sO,new T2(0,new T2(0,_cm,new T2(0,_sY,_t0)),_sN));});}};if(_sT>_sU){return new F(function(){return _sV(_sU,_sU);});}else{return new F(function(){return _sV(_sT,_sT);});}}else{return new F(function(){return A2(_sI,_sN,function(_t2){return new F(function(){return A1(_sO,new T2(0,new T2(0,_5i,_sP),E(_t2).b));});});});}};return B(_rS(_4l,_st,_sL));}),_t3=function(_t4,_t5){var _t6=new T(function(){return B(A2(_sw,_t4,function(_t7){return new F(function(){return _sf(_sG,_sH,E(_t7).b,_t5);});}));}),_t8=function(_t9){var _ta=new T(function(){var _tb=E(_t9),_tc=E(_tb.a),_td=E(_tb.b),_te=E(_td.a),_tf=E(_td.b),_tg=E(_td.c),_th=E(_td.d);return E(_t6);});return new T1(0,B(_p6(_st,_t9,function(_ti){return E(_ta);})));};return new T1(0,B(_pi(_st,_t8)));};return E(_t3);},_tj=1,_tk=function(_tl,_tm){var _tn=new T(function(){var _to=function(_tp,_tq,_tr){return new F(function(){return A1(_tr,new T2(0,new T2(0,_7,new T2(0,_tm,new T4(0,_tm,_tm,_tj,new T(function(){return E(E(E(_tp).b).d);})))),_tq));});};return B(_rS(_4l,_tl,_to));}),_ts=function(_tt,_tu){var _tv=new T(function(){return B(A2(_tn,_tt,_tu));}),_tw=function(_tx){var _ty=new T(function(){var _tz=E(_tx),_tA=E(_tz.a),_tB=E(_tz.b),_tC=E(_tB.a),_tD=E(_tB.b),_tE=E(_tB.c),_tF=E(_tB.d);return E(_tv);});return new T1(0,B(_p6(_tl,_tx,function(_tG){return E(_ty);})));};return new T1(0,B(_pi(_tl,_tw)));};return E(_ts);},_tH=function(_tI,_tJ){var _tK=E(_tI);if(!_tK._){return __Z;}else{var _tL=_tK.a,_tM=E(_tJ);return (_tM==1)?new T2(1,new T(function(){var _tN=E(_tL),_tO=E(_tN.b);return new T2(0,_tO,_tN);}),_6):new T2(1,new T(function(){var _tP=E(_tL),_tQ=E(_tP.b);return new T2(0,_tQ,_tP);}),new T(function(){return B(_tH(_tK.b,_tM-1|0));}));}},_tR=function(_tS,_tT){while(1){var _tU=E(_tS);if(!_tU._){return E(_tT);}else{var _tV=_tT+1|0;_tS=_tU.b;_tT=_tV;continue;}}},_tW=function(_tX,_tY,_tZ,_u0,_u1,_){var _u2=function(_,_u3){var _u4=E(_tY);switch(_u4._){case 0:return new F(function(){return A(_tZ,[new T2(0,_u3,_u4.a),_u0,_u1,_]);});break;case 1:var _u5=B(A1(_u4.a,_));return new F(function(){return A(_tZ,[new T2(0,_u3,_u5),_u0,_u1,_]);});break;case 2:var _u6=rMV(E(E(_u4.a).c)),_u7=E(_u6);if(!_u7._){var _u8=new T(function(){return B(A1(_u4.b,new T(function(){return B(_qv(_u7.a));})));});return new F(function(){return A(_tZ,[new T2(0,_u3,_u8),_u0,_u1,_]);});}else{return _7;}break;default:var _u9=rMV(E(E(_u4.a).c)),_ua=E(_u9);if(!_ua._){var _ub=B(A2(_u4.b,E(_ua.a).a,_));return new F(function(){return A(_tZ,[new T2(0,_u3,_ub),_u0,_u1,_]);});}else{return _7;}}},_uc=E(_tX);switch(_uc._){case 0:return new F(function(){return _u2(_,_uc.a);});break;case 1:var _ud=B(A1(_uc.a,_));return new F(function(){return _u2(_,_ud);});break;case 2:var _ue=rMV(E(E(_uc.a).c)),_uf=E(_ue);if(!_uf._){var _ug=new T(function(){return B(A1(_uc.b,new T(function(){return E(E(_uf.a).a);})));});return new F(function(){return _u2(_,_ug);});}else{return _7;}break;default:var _uh=rMV(E(E(_uc.a).c)),_ui=E(_uh);if(!_ui._){var _uj=B(A2(_uc.b,E(_ui.a).a,_));return new F(function(){return _u2(_,_uj);});}else{return _7;}}},_uk=new T(function(){return eval("(function(x,y,ctx,_){ctx.lineTo(x,y);})");}),_ul=function(_um,_un,_uo,_up,_){var _uq=__app4(E(_uk),_um,_un,_uo,E(_up));return new F(function(){return _qV(_);});},_ur=function(_us,_ut){var _uu=function(_uv,_uw,_ux,_){var _uy=E(_ut);return new F(function(){return _tW(_uy.a,_uy.b,function(_uz,_uA,_uB,_){var _uC=E(_uv),_uD=E(_uA),_uE=E(_uB),_uF=__app4(E(_qX),E(_uC.a),E(_uC.b),_uD,_uE),_uG=E(_uz);return new F(function(){return _ul(E(_uG.a),E(_uG.b),_uD,_uE,_);});},_uw,_ux,_);});};return new T3(0,_5k,function(_uH,_uI,_){var _uJ=E(_us);return new F(function(){return _tW(_uJ.a,_uJ.b,_uu,_uH,_uI,_);});},_7);},_uK=function(_uL,_uM,_uN,_uO){var _uP=E(_uO);if(!_uP._){return __Z;}else{var _uQ=E(_uP.b),_uR=new T(function(){return B(_uK(new T(function(){return E(_uL)+E(_uN);}),new T(function(){return E(_uM)+60;}),new T(function(){return E(_uN)/2;}),_uP.c));});return new F(function(){return _2(B(_uK(new T(function(){return E(_uL)-E(_uN);}),new T(function(){return E(_uM)+60;}),new T(function(){return E(_uN)/2;}),_uP.a)),new T2(1,new T4(0,new T2(0,_uL,_uM),new T2(0,E(_uQ.a).a,E(_uQ.b).a),_uP,new T(function(){return E(_uN)/2;})),_uR));});}},_uS=function(_uT,_uU,_uV,_uW){while(1){var _uX=E(_uW);if(!_uX._){var _uY=E(_uX.b);if(_uT>_uY){_uU=_uY;_uV=_uX.c;_uW=_uX.e;continue;}else{_uW=_uX.d;continue;}}else{return new T2(0,_uU,_uV);}}},_uZ=function(_v0,_v1){while(1){var _v2=E(_v1);if(!_v2._){var _v3=E(_v2.b);if(_v0>_v3){return new T1(1,B(_uS(_v0,_v3,_v2.c,_v2.e)));}else{_v1=_v2.d;continue;}}else{return __Z;}}},_v4=new T(function(){return eval("(function(ctx,_){ctx.restore();})");}),_v5=new T(function(){return eval("(function(ctx,_){ctx.save();})");}),_v6=new T(function(){return eval("(function(x,y,ctx,_){ctx.scale(x,y);})");}),_v7=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.strokeText(str,x,y);})");}),_v8=new T(function(){return eval("(function(str,x,y,ctx,_){ctx.fillText(str,x,y);})");}),_v9=new T(function(){return eval("(function(x,y,ctx,_){ctx.translate(x,y);})");}),_va="alphabetic",_vb="middle",_vc="hanging",_vd="right",_ve="center",_vf="left",_vg="(function(fn,a,b,ctx){ctx.font=\"10px \"+fn;ctx.textAlign=a;ctx.textBaseline=b;})",_vh=function(_vi,_vj,_vk,_vl,_vm,_vn,_vo){var _vp=function(_vq,_vr,_vs,_){var _vt=function(_vu,_vv,_vw,_){var _vx=function(_vy,_vz,_vA,_){var _vB=function(_vC,_vD,_vE,_){var _vF=E(_vD),_vG=E(_vE),_vH=__app2(E(_v5),_vF,_vG),_vI=function(_vJ){var _vK=function(_vL){var _vM=eval(E(_vg)),_vN=__app4(E(_vM),E(_vi),_vJ,_vL,_vF),_vO=__app4(E(_v9),E(_vu),E(_vy),_vF,_vG),_vP=E(_vC)/10,_vQ=__app4(E(_v6),_vP,_vP,_vF,_vG);if(!_vG){var _vR=__app5(E(_v7),toJSStr(E(_vq)),0,0,_vF,false),_vS=__app2(E(_v4),_vF,false);return new F(function(){return _qV(_);});}else{var _vT=__app5(E(_v8),toJSStr(E(_vq)),0,0,_vF,true),_vU=__app2(E(_v4),_vF,true);return new F(function(){return _qV(_);});}};switch(E(_vl)){case 0:return new F(function(){return _vK(E(_vc));});break;case 1:return new F(function(){return _vK(E(_vb));});break;default:return new F(function(){return _vK(E(_va));});}};switch(E(_vk)){case 0:return new F(function(){return _vI(E(_vf));});break;case 1:return new F(function(){return _vI(E(_ve));});break;default:return new F(function(){return _vI(E(_vd));});}};return new F(function(){return _qx(_vo,_vB,_vz,_vA,_);});};return new F(function(){return _qx(_vn,_vx,_vv,_vw,_);});};return new F(function(){return _qx(_vm,_vt,_vr,_vs,_);});};return new T3(0,_5k,function(_rD,_rE,_){return new F(function(){return _qx(_vj,_vp,_rD,_rE,_);});},_7);},_vV=function(_vW,_vX,_vY,_vZ,_w0,_w1){return (_vW!=_vZ)?true:(E(_vX)!=E(_w0))?true:(E(_vY)!=E(_w1))?true:false;},_w2=function(_w3,_w4){var _w5=E(_w3),_w6=E(_w4);return new F(function(){return _vV(E(_w5.a),_w5.b,_w5.c,E(_w6.a),_w6.b,_w6.c);});},_w7=function(_w8,_w9){return E(_w8)==E(_w9);},_wa=function(_wb,_wc,_wd,_we,_wf,_wg){if(_wb!=_we){return false;}else{if(E(_wc)!=E(_wf)){return false;}else{return new F(function(){return _w7(_wd,_wg);});}}},_wh=function(_wi,_wj){var _wk=E(_wi),_wl=E(_wj);return new F(function(){return _wa(E(_wk.a),_wk.b,_wk.c,E(_wl.a),_wl.b,_wl.c);});},_wm=new T2(0,_wh,_w2),_wn=__Z,_wo=function(_wp){return E(E(_wp).b);},_wq=new T0(1),_wr=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_ws=function(_wt){return new F(function(){return err(_wr);});},_wu=new T(function(){return B(_ws(_));}),_wv=function(_ww,_wx,_wy,_wz){var _wA=E(_wz);if(!_wA._){var _wB=_wA.a,_wC=E(_wy);if(!_wC._){var _wD=_wC.a,_wE=_wC.b,_wF=_wC.c;if(_wD<=(imul(3,_wB)|0)){return new T5(0,(1+_wD|0)+_wB|0,E(_ww),_wx,E(_wC),E(_wA));}else{var _wG=E(_wC.d);if(!_wG._){var _wH=_wG.a,_wI=E(_wC.e);if(!_wI._){var _wJ=_wI.a,_wK=_wI.b,_wL=_wI.c,_wM=_wI.d;if(_wJ>=(imul(2,_wH)|0)){var _wN=function(_wO){var _wP=E(_wI.e);return (_wP._==0)?new T5(0,(1+_wD|0)+_wB|0,E(_wK),_wL,E(new T5(0,(1+_wH|0)+_wO|0,E(_wE),_wF,E(_wG),E(_wM))),E(new T5(0,(1+_wB|0)+_wP.a|0,E(_ww),_wx,E(_wP),E(_wA)))):new T5(0,(1+_wD|0)+_wB|0,E(_wK),_wL,E(new T5(0,(1+_wH|0)+_wO|0,E(_wE),_wF,E(_wG),E(_wM))),E(new T5(0,1+_wB|0,E(_ww),_wx,E(_wq),E(_wA))));},_wQ=E(_wM);if(!_wQ._){return new F(function(){return _wN(_wQ.a);});}else{return new F(function(){return _wN(0);});}}else{return new T5(0,(1+_wD|0)+_wB|0,E(_wE),_wF,E(_wG),E(new T5(0,(1+_wB|0)+_wJ|0,E(_ww),_wx,E(_wI),E(_wA))));}}else{return E(_wu);}}else{return E(_wu);}}}else{return new T5(0,1+_wB|0,E(_ww),_wx,E(_wq),E(_wA));}}else{var _wR=E(_wy);if(!_wR._){var _wS=_wR.a,_wT=_wR.b,_wU=_wR.c,_wV=_wR.e,_wW=E(_wR.d);if(!_wW._){var _wX=_wW.a,_wY=E(_wV);if(!_wY._){var _wZ=_wY.a,_x0=_wY.b,_x1=_wY.c,_x2=_wY.d;if(_wZ>=(imul(2,_wX)|0)){var _x3=function(_x4){var _x5=E(_wY.e);return (_x5._==0)?new T5(0,1+_wS|0,E(_x0),_x1,E(new T5(0,(1+_wX|0)+_x4|0,E(_wT),_wU,E(_wW),E(_x2))),E(new T5(0,1+_x5.a|0,E(_ww),_wx,E(_x5),E(_wq)))):new T5(0,1+_wS|0,E(_x0),_x1,E(new T5(0,(1+_wX|0)+_x4|0,E(_wT),_wU,E(_wW),E(_x2))),E(new T5(0,1,E(_ww),_wx,E(_wq),E(_wq))));},_x6=E(_x2);if(!_x6._){return new F(function(){return _x3(_x6.a);});}else{return new F(function(){return _x3(0);});}}else{return new T5(0,1+_wS|0,E(_wT),_wU,E(_wW),E(new T5(0,1+_wZ|0,E(_ww),_wx,E(_wY),E(_wq))));}}else{return new T5(0,3,E(_wT),_wU,E(_wW),E(new T5(0,1,E(_ww),_wx,E(_wq),E(_wq))));}}else{var _x7=E(_wV);return (_x7._==0)?new T5(0,3,E(_x7.b),_x7.c,E(new T5(0,1,E(_wT),_wU,E(_wq),E(_wq))),E(new T5(0,1,E(_ww),_wx,E(_wq),E(_wq)))):new T5(0,2,E(_ww),_wx,E(_wR),E(_wq));}}else{return new T5(0,1,E(_ww),_wx,E(_wq),E(_wq));}}},_x8=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_x9=function(_xa){return new F(function(){return err(_x8);});},_xb=new T(function(){return B(_x9(_));}),_xc=function(_xd,_xe,_xf,_xg){var _xh=E(_xf);if(!_xh._){var _xi=_xh.a,_xj=E(_xg);if(!_xj._){var _xk=_xj.a,_xl=_xj.b,_xm=_xj.c;if(_xk<=(imul(3,_xi)|0)){return new T5(0,(1+_xi|0)+_xk|0,E(_xd),_xe,E(_xh),E(_xj));}else{var _xn=E(_xj.d);if(!_xn._){var _xo=_xn.a,_xp=_xn.b,_xq=_xn.c,_xr=_xn.d,_xs=E(_xj.e);if(!_xs._){var _xt=_xs.a;if(_xo>=(imul(2,_xt)|0)){var _xu=function(_xv){var _xw=E(_xd),_xx=E(_xn.e);return (_xx._==0)?new T5(0,(1+_xi|0)+_xk|0,E(_xp),_xq,E(new T5(0,(1+_xi|0)+_xv|0,E(_xw),_xe,E(_xh),E(_xr))),E(new T5(0,(1+_xt|0)+_xx.a|0,E(_xl),_xm,E(_xx),E(_xs)))):new T5(0,(1+_xi|0)+_xk|0,E(_xp),_xq,E(new T5(0,(1+_xi|0)+_xv|0,E(_xw),_xe,E(_xh),E(_xr))),E(new T5(0,1+_xt|0,E(_xl),_xm,E(_wq),E(_xs))));},_xy=E(_xr);if(!_xy._){return new F(function(){return _xu(_xy.a);});}else{return new F(function(){return _xu(0);});}}else{return new T5(0,(1+_xi|0)+_xk|0,E(_xl),_xm,E(new T5(0,(1+_xi|0)+_xo|0,E(_xd),_xe,E(_xh),E(_xn))),E(_xs));}}else{return E(_xb);}}else{return E(_xb);}}}else{return new T5(0,1+_xi|0,E(_xd),_xe,E(_xh),E(_wq));}}else{var _xz=E(_xg);if(!_xz._){var _xA=_xz.a,_xB=_xz.b,_xC=_xz.c,_xD=_xz.e,_xE=E(_xz.d);if(!_xE._){var _xF=_xE.a,_xG=_xE.b,_xH=_xE.c,_xI=_xE.d,_xJ=E(_xD);if(!_xJ._){var _xK=_xJ.a;if(_xF>=(imul(2,_xK)|0)){var _xL=function(_xM){var _xN=E(_xd),_xO=E(_xE.e);return (_xO._==0)?new T5(0,1+_xA|0,E(_xG),_xH,E(new T5(0,1+_xM|0,E(_xN),_xe,E(_wq),E(_xI))),E(new T5(0,(1+_xK|0)+_xO.a|0,E(_xB),_xC,E(_xO),E(_xJ)))):new T5(0,1+_xA|0,E(_xG),_xH,E(new T5(0,1+_xM|0,E(_xN),_xe,E(_wq),E(_xI))),E(new T5(0,1+_xK|0,E(_xB),_xC,E(_wq),E(_xJ))));},_xP=E(_xI);if(!_xP._){return new F(function(){return _xL(_xP.a);});}else{return new F(function(){return _xL(0);});}}else{return new T5(0,1+_xA|0,E(_xB),_xC,E(new T5(0,1+_xF|0,E(_xd),_xe,E(_wq),E(_xE))),E(_xJ));}}else{return new T5(0,3,E(_xG),_xH,E(new T5(0,1,E(_xd),_xe,E(_wq),E(_wq))),E(new T5(0,1,E(_xB),_xC,E(_wq),E(_wq))));}}else{var _xQ=E(_xD);return (_xQ._==0)?new T5(0,3,E(_xB),_xC,E(new T5(0,1,E(_xd),_xe,E(_wq),E(_wq))),E(_xQ)):new T5(0,2,E(_xd),_xe,E(_wq),E(_xz));}}else{return new T5(0,1,E(_xd),_xe,E(_wq),E(_wq));}}},_xR=function(_xS,_xT){return new T5(0,1,E(_xS),_xT,E(_wq),E(_wq));},_xU=function(_xV,_xW,_xX){var _xY=E(_xX);if(!_xY._){return new F(function(){return _xc(_xY.b,_xY.c,_xY.d,B(_xU(_xV,_xW,_xY.e)));});}else{return new F(function(){return _xR(_xV,_xW);});}},_xZ=function(_y0,_y1,_y2){var _y3=E(_y2);if(!_y3._){return new F(function(){return _wv(_y3.b,_y3.c,B(_xZ(_y0,_y1,_y3.d)),_y3.e);});}else{return new F(function(){return _xR(_y0,_y1);});}},_y4=function(_y5,_y6,_y7,_y8,_y9,_ya,_yb){return new F(function(){return _wv(_y8,_y9,B(_xZ(_y5,_y6,_ya)),_yb);});},_yc=function(_yd,_ye,_yf,_yg,_yh,_yi,_yj,_yk){var _yl=E(_yf);if(!_yl._){var _ym=_yl.a,_yn=_yl.b,_yo=_yl.c,_yp=_yl.d,_yq=_yl.e;if((imul(3,_ym)|0)>=_yg){if((imul(3,_yg)|0)>=_ym){return new T5(0,(_ym+_yg|0)+1|0,E(_yd),_ye,E(_yl),E(new T5(0,_yg,E(_yh),_yi,E(_yj),E(_yk))));}else{return new F(function(){return _xc(_yn,_yo,_yp,B(_yc(_yd,_ye,_yq,_yg,_yh,_yi,_yj,_yk)));});}}else{return new F(function(){return _wv(_yh,_yi,B(_yr(_yd,_ye,_ym,_yn,_yo,_yp,_yq,_yj)),_yk);});}}else{return new F(function(){return _y4(_yd,_ye,_yg,_yh,_yi,_yj,_yk);});}},_yr=function(_ys,_yt,_yu,_yv,_yw,_yx,_yy,_yz){var _yA=E(_yz);if(!_yA._){var _yB=_yA.a,_yC=_yA.b,_yD=_yA.c,_yE=_yA.d,_yF=_yA.e;if((imul(3,_yu)|0)>=_yB){if((imul(3,_yB)|0)>=_yu){return new T5(0,(_yu+_yB|0)+1|0,E(_ys),_yt,E(new T5(0,_yu,E(_yv),_yw,E(_yx),E(_yy))),E(_yA));}else{return new F(function(){return _xc(_yv,_yw,_yx,B(_yc(_ys,_yt,_yy,_yB,_yC,_yD,_yE,_yF)));});}}else{return new F(function(){return _wv(_yC,_yD,B(_yr(_ys,_yt,_yu,_yv,_yw,_yx,_yy,_yE)),_yF);});}}else{return new F(function(){return _xU(_ys,_yt,new T5(0,_yu,E(_yv),_yw,E(_yx),E(_yy)));});}},_yG=function(_yH,_yI,_yJ,_yK){var _yL=E(_yJ);if(!_yL._){var _yM=_yL.a,_yN=_yL.b,_yO=_yL.c,_yP=_yL.d,_yQ=_yL.e,_yR=E(_yK);if(!_yR._){var _yS=_yR.a,_yT=_yR.b,_yU=_yR.c,_yV=_yR.d,_yW=_yR.e;if((imul(3,_yM)|0)>=_yS){if((imul(3,_yS)|0)>=_yM){return new T5(0,(_yM+_yS|0)+1|0,E(_yH),_yI,E(_yL),E(_yR));}else{return new F(function(){return _xc(_yN,_yO,_yP,B(_yc(_yH,_yI,_yQ,_yS,_yT,_yU,_yV,_yW)));});}}else{return new F(function(){return _wv(_yT,_yU,B(_yr(_yH,_yI,_yM,_yN,_yO,_yP,_yQ,_yV)),_yW);});}}else{return new F(function(){return _xU(_yH,_yI,_yL);});}}else{return new F(function(){return _xZ(_yH,_yI,_yK);});}},_yX=function(_yY,_yZ,_z0){var _z1=E(_yZ);if(!_z1._){return E(_z0);}else{var _z2=function(_z3,_z4){while(1){var _z5=E(_z4);if(!_z5._){var _z6=_z5.b,_z7=_z5.e;switch(B(A3(_wo,_yY,_z3,_z6))){case 0:return new F(function(){return _yG(_z6,_z5.c,B(_z2(_z3,_z5.d)),_z7);});break;case 1:return E(_z7);default:_z4=_z7;continue;}}else{return new T0(1);}}};return new F(function(){return _z2(_z1.a,_z0);});}},_z8=function(_z9,_za,_zb){var _zc=E(_za);if(!_zc._){return E(_zb);}else{var _zd=function(_ze,_zf){while(1){var _zg=E(_zf);if(!_zg._){var _zh=_zg.b,_zi=_zg.d;switch(B(A3(_wo,_z9,_zh,_ze))){case 0:return new F(function(){return _yG(_zh,_zg.c,_zi,B(_zd(_ze,_zg.e)));});break;case 1:return E(_zi);default:_zf=_zi;continue;}}else{return new T0(1);}}};return new F(function(){return _zd(_zc.a,_zb);});}},_zj=function(_zk,_zl,_zm,_zn){var _zo=E(_zl),_zp=E(_zn);if(!_zp._){var _zq=_zp.b,_zr=_zp.c,_zs=_zp.d,_zt=_zp.e;switch(B(A3(_wo,_zk,_zo,_zq))){case 0:return new F(function(){return _wv(_zq,_zr,B(_zj(_zk,_zo,_zm,_zs)),_zt);});break;case 1:return E(_zp);default:return new F(function(){return _xc(_zq,_zr,_zs,B(_zj(_zk,_zo,_zm,_zt)));});}}else{return new T5(0,1,E(_zo),_zm,E(_wq),E(_wq));}},_zu=function(_zv,_zw,_zx,_zy){return new F(function(){return _zj(_zv,_zw,_zx,_zy);});},_zz=function(_zA){return E(E(_zA).d);},_zB=function(_zC){return E(E(_zC).f);},_zD=function(_zE,_zF,_zG,_zH){var _zI=E(_zF);if(!_zI._){var _zJ=E(_zG);if(!_zJ._){return E(_zH);}else{var _zK=function(_zL,_zM){while(1){var _zN=E(_zM);if(!_zN._){if(!B(A3(_zB,_zE,_zN.b,_zL))){return E(_zN);}else{_zM=_zN.d;continue;}}else{return new T0(1);}}};return new F(function(){return _zK(_zJ.a,_zH);});}}else{var _zO=_zI.a,_zP=E(_zG);if(!_zP._){var _zQ=function(_zR,_zS){while(1){var _zT=E(_zS);if(!_zT._){if(!B(A3(_zz,_zE,_zT.b,_zR))){return E(_zT);}else{_zS=_zT.e;continue;}}else{return new T0(1);}}};return new F(function(){return _zQ(_zO,_zH);});}else{var _zU=function(_zV,_zW,_zX){while(1){var _zY=E(_zX);if(!_zY._){var _zZ=_zY.b;if(!B(A3(_zz,_zE,_zZ,_zV))){if(!B(A3(_zB,_zE,_zZ,_zW))){return E(_zY);}else{_zX=_zY.d;continue;}}else{_zX=_zY.e;continue;}}else{return new T0(1);}}};return new F(function(){return _zU(_zO,_zP.a,_zH);});}}},_A0=function(_A1,_A2,_A3,_A4,_A5){var _A6=E(_A5);if(!_A6._){var _A7=_A6.b,_A8=_A6.c,_A9=_A6.d,_Aa=_A6.e,_Ab=E(_A4);if(!_Ab._){var _Ac=_Ab.b,_Ad=function(_Ae){var _Af=new T1(1,E(_Ac));return new F(function(){return _yG(_Ac,_Ab.c,B(_A0(_A1,_A2,_Af,_Ab.d,B(_zD(_A1,_A2,_Af,_A6)))),B(_A0(_A1,_Af,_A3,_Ab.e,B(_zD(_A1,_Af,_A3,_A6)))));});};if(!E(_A9)._){return new F(function(){return _Ad(_);});}else{if(!E(_Aa)._){return new F(function(){return _Ad(_);});}else{return new F(function(){return _zu(_A1,_A7,_A8,_Ab);});}}}else{return new F(function(){return _yG(_A7,_A8,B(_yX(_A1,_A2,_A9)),B(_z8(_A1,_A3,_Aa)));});}}else{return E(_A4);}},_Ag=function(_Ah,_Ai,_Aj,_Ak,_Al,_Am,_An,_Ao,_Ap,_Aq,_Ar,_As,_At){var _Au=function(_Av){var _Aw=new T1(1,E(_Al));return new F(function(){return _yG(_Al,_Am,B(_A0(_Ah,_Ai,_Aw,_An,B(_zD(_Ah,_Ai,_Aw,new T5(0,_Ap,E(_Aq),_Ar,E(_As),E(_At)))))),B(_A0(_Ah,_Aw,_Aj,_Ao,B(_zD(_Ah,_Aw,_Aj,new T5(0,_Ap,E(_Aq),_Ar,E(_As),E(_At)))))));});};if(!E(_As)._){return new F(function(){return _Au(_);});}else{if(!E(_At)._){return new F(function(){return _Au(_);});}else{return new F(function(){return _zu(_Ah,_Aq,_Ar,new T5(0,_Ak,E(_Al),_Am,E(_An),E(_Ao)));});}}},_Ax=function(_Ay,_Az){var _AA=E(_Ay);if(!_AA._){var _AB=E(_Az);if(!_AB._){return new F(function(){return _Ag(_bP,_wn,_wn,_AA.a,_AA.b,_AA.c,_AA.d,_AA.e,_AB.a,_AB.b,_AB.c,_AB.d,_AB.e);});}else{return E(_AA);}}else{return E(_Az);}},_AC=function(_AD,_AE,_AF,_AG){return (_AD!=_AF)?true:(E(_AE)!=E(_AG))?true:false;},_AH=function(_AI,_AJ){var _AK=E(_AI),_AL=E(_AJ);return new F(function(){return _AC(E(_AK.a),_AK.b,E(_AL.a),_AL.b);});},_AM=function(_AN,_AO,_AP,_AQ){if(_AN!=_AP){return false;}else{return new F(function(){return _bk(_AO,_AQ);});}},_AR=function(_AS,_AT){var _AU=E(_AS),_AV=E(_AT);return new F(function(){return _AM(E(_AU.a),_AU.b,E(_AV.a),_AV.b);});},_AW=new T2(0,_AR,_AH),_AX=function(_AY,_AZ,_B0,_B1,_B2,_B3,_B4,_B5,_B6,_B7,_B8,_B9,_Ba,_Bb,_Bc,_Bd,_Be,_Bf,_Bg,_Bh,_Bi,_Bj,_Bk,_Bl){if(_AY!=_Ba){return false;}else{if(_AZ!=_Bb){return false;}else{if(_B0!=_Bc){return false;}else{if(_B1!=_Bd){return false;}else{if(_B2!=_Be){return false;}else{if(_B3!=_Bf){return false;}else{if(_B4!=_Bg){return false;}else{if(_B5!=_Bh){return false;}else{if(_B6!=_Bi){return false;}else{if(_B7!=_Bj){return false;}else{if(E(_B8)!=E(_Bk)){return false;}else{return new F(function(){return _bk(_B9,_Bl);});}}}}}}}}}}}},_Bm=function(_Bn,_Bo){var _Bp=E(_Bn),_Bq=E(_Bp.a),_Br=E(_Bp.b),_Bs=E(_Bp.c),_Bt=E(_Bp.e),_Bu=E(_Bo),_Bv=E(_Bu.a),_Bw=E(_Bu.b),_Bx=E(_Bu.c),_By=E(_Bu.e);return new F(function(){return _AX(_Bq.a,_Bq.b,_Bq.c,_Br.a,_Br.b,_Br.c,_Bs.a,_Bs.b,_Bs.c,_Bp.d,_Bt.a,_Bt.b,_Bv.a,_Bv.b,_Bv.c,_Bw.a,_Bw.b,_Bw.c,_Bx.a,_Bx.b,_Bx.c,_Bu.d,_By.a,_By.b);});},_Bz=function(_BA,_BB,_BC,_BD,_BE,_BF){if(_BA!=_BD){return false;}else{var _BG=E(_BB),_BH=E(_BE);if(E(_BG.a)!=E(_BH.a)){return false;}else{if(E(_BG.b)!=E(_BH.b)){return false;}else{if(E(_BG.c)!=E(_BH.c)){return false;}else{return new F(function(){return _Bm(_BC,_BF);});}}}}},_BI=function(_BJ,_BK){var _BL=E(_BJ),_BM=E(_BK);return new F(function(){return _Bz(E(_BL.a),_BL.b,_BL.c,E(_BM.a),_BM.b,_BM.c);});},_BN=function(_BO,_BP,_BQ,_BR,_BS,_BT){if(_BO!=_BR){return true;}else{var _BU=E(_BP),_BV=E(_BS);if(E(_BU.a)!=E(_BV.a)){return true;}else{if(E(_BU.b)!=E(_BV.b)){return true;}else{if(E(_BU.c)!=E(_BV.c)){return true;}else{var _BW=E(_BQ),_BX=E(_BW.a),_BY=E(_BW.b),_BZ=E(_BW.c),_C0=E(_BW.e),_C1=E(_BT),_C2=E(_C1.a),_C3=E(_C1.b),_C4=E(_C1.c),_C5=E(_C1.e);return (_BX.a!=_C2.a)?true:(_BX.b!=_C2.b)?true:(_BX.c!=_C2.c)?true:(_BY.a!=_C3.a)?true:(_BY.b!=_C3.b)?true:(_BY.c!=_C3.c)?true:(_BZ.a!=_C4.a)?true:(_BZ.b!=_C4.b)?true:(_BZ.c!=_C4.c)?true:(_BW.d!=_C1.d)?true:(E(_C0.a)!=E(_C5.a))?true:(E(_C0.b)!=E(_C5.b))?true:false;}}}}},_C6=function(_C7,_C8){var _C9=E(_C7),_Ca=E(_C8);return new F(function(){return _BN(E(_C9.a),_C9.b,_C9.c,E(_Ca.a),_Ca.b,_Ca.c);});},_Cb=new T2(0,_BI,_C6),_Cc=function(_Cd,_Ce,_Cf,_Cg,_Ch,_Ci,_Cj,_Ck,_Cl,_Cm,_Cn,_Co,_Cp,_Cq,_Cr,_Cs,_Ct,_Cu,_Cv,_Cw,_Cx,_Cy,_Cz,_CA){if(_Cd>=_Cp){if(_Cd!=_Cp){return 2;}else{if(_Ce>=_Cq){if(_Ce!=_Cq){return 2;}else{if(_Cf>=_Cr){if(_Cf!=_Cr){return 2;}else{if(_Cg>=_Cs){if(_Cg!=_Cs){return 2;}else{if(_Ch>=_Ct){if(_Ch!=_Ct){return 2;}else{if(_Ci>=_Cu){if(_Ci!=_Cu){return 2;}else{if(_Cj>=_Cv){if(_Cj!=_Cv){return 2;}else{if(_Ck>=_Cw){if(_Ck!=_Cw){return 2;}else{if(_Cl>=_Cx){if(_Cl!=_Cx){return 2;}else{if(_Cm>=_Cy){if(_Cm!=_Cy){return 2;}else{var _CB=E(_Cn),_CC=E(_Cz);if(_CB>=_CC){if(_CB!=_CC){return 2;}else{return new F(function(){return _bA(_Co,_CA);});}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}},_CD=function(_CE,_CF){var _CG=E(_CE),_CH=E(_CG.a),_CI=E(_CG.b),_CJ=E(_CG.c),_CK=E(_CG.e),_CL=E(_CF),_CM=E(_CL.a),_CN=E(_CL.b),_CO=E(_CL.c),_CP=E(_CL.e);return new F(function(){return _Cc(_CH.a,_CH.b,_CH.c,_CI.a,_CI.b,_CI.c,_CJ.a,_CJ.b,_CJ.c,_CG.d,_CK.a,_CK.b,_CM.a,_CM.b,_CM.c,_CN.a,_CN.b,_CN.c,_CO.a,_CO.b,_CO.c,_CL.d,_CP.a,_CP.b);});},_CQ=function(_CR,_CS,_CT,_CU,_CV,_CW){if(_CR>=_CU){if(_CR!=_CU){return 2;}else{var _CX=E(_CS),_CY=E(_CV),_CZ=E(_CX.a),_D0=E(_CY.a);if(_CZ>=_D0){if(_CZ!=_D0){return 2;}else{var _D1=E(_CX.b),_D2=E(_CY.b);if(_D1>=_D2){if(_D1!=_D2){return 2;}else{var _D3=E(_CX.c),_D4=E(_CY.c);if(_D3>=_D4){if(_D3!=_D4){return 2;}else{return new F(function(){return _CD(_CT,_CW);});}}else{return 0;}}}else{return 0;}}}else{return 0;}}}else{return 0;}},_D5=function(_D6,_D7){var _D8=E(_D6),_D9=E(_D7);return new F(function(){return _CQ(E(_D8.a),_D8.b,_D8.c,E(_D9.a),_D9.b,_D9.c);});},_Da=function(_Db,_Dc,_Dd,_De,_Df,_Dg,_Dh,_Di,_Dj,_Dk,_Dl,_Dm,_Dn,_Do,_Dp,_Dq,_Dr,_Ds,_Dt,_Du,_Dv,_Dw,_Dx,_Dy){if(_Db>=_Dn){if(_Db!=_Dn){return false;}else{if(_Dc>=_Do){if(_Dc!=_Do){return false;}else{if(_Dd>=_Dp){if(_Dd!=_Dp){return false;}else{if(_De>=_Dq){if(_De!=_Dq){return false;}else{if(_Df>=_Dr){if(_Df!=_Dr){return false;}else{if(_Dg>=_Ds){if(_Dg!=_Ds){return false;}else{if(_Dh>=_Dt){if(_Dh!=_Dt){return false;}else{if(_Di>=_Du){if(_Di!=_Du){return false;}else{if(_Dj>=_Dv){if(_Dj!=_Dv){return false;}else{if(_Dk>=_Dw){if(_Dk!=_Dw){return false;}else{var _Dz=E(_Dl),_DA=E(_Dx);if(_Dz>=_DA){if(_Dz!=_DA){return false;}else{return new F(function(){return _bo(_Dm,_Dy);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_DB=function(_DC,_DD){var _DE=E(_DC),_DF=E(_DE.a),_DG=E(_DE.b),_DH=E(_DE.c),_DI=E(_DE.e),_DJ=E(_DD),_DK=E(_DJ.a),_DL=E(_DJ.b),_DM=E(_DJ.c),_DN=E(_DJ.e);return new F(function(){return _Da(_DF.a,_DF.b,_DF.c,_DG.a,_DG.b,_DG.c,_DH.a,_DH.b,_DH.c,_DE.d,_DI.a,_DI.b,_DK.a,_DK.b,_DK.c,_DL.a,_DL.b,_DL.c,_DM.a,_DM.b,_DM.c,_DJ.d,_DN.a,_DN.b);});},_DO=function(_DP,_DQ,_DR,_DS,_DT,_DU){if(_DP>=_DS){if(_DP!=_DS){return false;}else{var _DV=E(_DQ),_DW=E(_DT),_DX=E(_DV.a),_DY=E(_DW.a);if(_DX>=_DY){if(_DX!=_DY){return false;}else{var _DZ=E(_DV.b),_E0=E(_DW.b);if(_DZ>=_E0){if(_DZ!=_E0){return false;}else{var _E1=E(_DV.c),_E2=E(_DW.c);if(_E1>=_E2){if(_E1!=_E2){return false;}else{return new F(function(){return _DB(_DR,_DU);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_E3=function(_E4,_E5){var _E6=E(_E4),_E7=E(_E5);return new F(function(){return _DO(E(_E6.a),_E6.b,_E6.c,E(_E7.a),_E7.b,_E7.c);});},_E8=function(_E9,_Ea,_Eb,_Ec,_Ed,_Ee,_Ef,_Eg,_Eh,_Ei,_Ej,_Ek,_El,_Em,_En,_Eo,_Ep,_Eq,_Er,_Es,_Et,_Eu,_Ev,_Ew){if(_E9>=_El){if(_E9!=_El){return false;}else{if(_Ea>=_Em){if(_Ea!=_Em){return false;}else{if(_Eb>=_En){if(_Eb!=_En){return false;}else{if(_Ec>=_Eo){if(_Ec!=_Eo){return false;}else{if(_Ed>=_Ep){if(_Ed!=_Ep){return false;}else{if(_Ee>=_Eq){if(_Ee!=_Eq){return false;}else{if(_Ef>=_Er){if(_Ef!=_Er){return false;}else{if(_Eg>=_Es){if(_Eg!=_Es){return false;}else{if(_Eh>=_Et){if(_Eh!=_Et){return false;}else{if(_Ei>=_Eu){if(_Ei!=_Eu){return false;}else{var _Ex=E(_Ej),_Ey=E(_Ev);if(_Ex>=_Ey){if(_Ex!=_Ey){return false;}else{return new F(function(){return _br(_Ek,_Ew);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_Ez=function(_EA,_EB){var _EC=E(_EA),_ED=E(_EC.a),_EE=E(_EC.b),_EF=E(_EC.c),_EG=E(_EC.e),_EH=E(_EB),_EI=E(_EH.a),_EJ=E(_EH.b),_EK=E(_EH.c),_EL=E(_EH.e);return new F(function(){return _E8(_ED.a,_ED.b,_ED.c,_EE.a,_EE.b,_EE.c,_EF.a,_EF.b,_EF.c,_EC.d,_EG.a,_EG.b,_EI.a,_EI.b,_EI.c,_EJ.a,_EJ.b,_EJ.c,_EK.a,_EK.b,_EK.c,_EH.d,_EL.a,_EL.b);});},_EM=function(_EN,_EO,_EP,_EQ,_ER,_ES){if(_EN>=_EQ){if(_EN!=_EQ){return false;}else{var _ET=E(_EO),_EU=E(_ER),_EV=E(_ET.a),_EW=E(_EU.a);if(_EV>=_EW){if(_EV!=_EW){return false;}else{var _EX=E(_ET.b),_EY=E(_EU.b);if(_EX>=_EY){if(_EX!=_EY){return false;}else{var _EZ=E(_ET.c),_F0=E(_EU.c);if(_EZ>=_F0){if(_EZ!=_F0){return false;}else{return new F(function(){return _Ez(_EP,_ES);});}}else{return true;}}}else{return true;}}}else{return true;}}}else{return true;}},_F1=function(_F2,_F3){var _F4=E(_F2),_F5=E(_F3);return new F(function(){return _EM(E(_F4.a),_F4.b,_F4.c,E(_F5.a),_F5.b,_F5.c);});},_F6=function(_F7,_F8,_F9,_Fa,_Fb,_Fc,_Fd,_Fe,_Ff,_Fg,_Fh,_Fi,_Fj,_Fk,_Fl,_Fm,_Fn,_Fo,_Fp,_Fq,_Fr,_Fs,_Ft,_Fu){if(_F7>=_Fj){if(_F7!=_Fj){return true;}else{if(_F8>=_Fk){if(_F8!=_Fk){return true;}else{if(_F9>=_Fl){if(_F9!=_Fl){return true;}else{if(_Fa>=_Fm){if(_Fa!=_Fm){return true;}else{if(_Fb>=_Fn){if(_Fb!=_Fn){return true;}else{if(_Fc>=_Fo){if(_Fc!=_Fo){return true;}else{if(_Fd>=_Fp){if(_Fd!=_Fp){return true;}else{if(_Fe>=_Fq){if(_Fe!=_Fq){return true;}else{if(_Ff>=_Fr){if(_Ff!=_Fr){return true;}else{if(_Fg>=_Fs){if(_Fg!=_Fs){return true;}else{var _Fv=E(_Fh),_Fw=E(_Ft);if(_Fv>=_Fw){if(_Fv!=_Fw){return true;}else{return new F(function(){return _bu(_Fi,_Fu);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_Fx=function(_Fy,_Fz){var _FA=E(_Fy),_FB=E(_FA.a),_FC=E(_FA.b),_FD=E(_FA.c),_FE=E(_FA.e),_FF=E(_Fz),_FG=E(_FF.a),_FH=E(_FF.b),_FI=E(_FF.c),_FJ=E(_FF.e);return new F(function(){return _F6(_FB.a,_FB.b,_FB.c,_FC.a,_FC.b,_FC.c,_FD.a,_FD.b,_FD.c,_FA.d,_FE.a,_FE.b,_FG.a,_FG.b,_FG.c,_FH.a,_FH.b,_FH.c,_FI.a,_FI.b,_FI.c,_FF.d,_FJ.a,_FJ.b);});},_FK=function(_FL,_FM,_FN,_FO,_FP,_FQ){if(_FL>=_FO){if(_FL!=_FO){return true;}else{var _FR=E(_FM),_FS=E(_FP),_FT=E(_FR.a),_FU=E(_FS.a);if(_FT>=_FU){if(_FT!=_FU){return true;}else{var _FV=E(_FR.b),_FW=E(_FS.b);if(_FV>=_FW){if(_FV!=_FW){return true;}else{var _FX=E(_FR.c),_FY=E(_FS.c);if(_FX>=_FY){if(_FX!=_FY){return true;}else{return new F(function(){return _Fx(_FN,_FQ);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_FZ=function(_G0,_G1){var _G2=E(_G0),_G3=E(_G1);return new F(function(){return _FK(E(_G2.a),_G2.b,_G2.c,E(_G3.a),_G3.b,_G3.c);});},_G4=function(_G5,_G6,_G7,_G8,_G9,_Ga,_Gb,_Gc,_Gd,_Ge,_Gf,_Gg,_Gh,_Gi,_Gj,_Gk,_Gl,_Gm,_Gn,_Go,_Gp,_Gq,_Gr,_Gs){if(_G5>=_Gh){if(_G5!=_Gh){return true;}else{if(_G6>=_Gi){if(_G6!=_Gi){return true;}else{if(_G7>=_Gj){if(_G7!=_Gj){return true;}else{if(_G8>=_Gk){if(_G8!=_Gk){return true;}else{if(_G9>=_Gl){if(_G9!=_Gl){return true;}else{if(_Ga>=_Gm){if(_Ga!=_Gm){return true;}else{if(_Gb>=_Gn){if(_Gb!=_Gn){return true;}else{if(_Gc>=_Go){if(_Gc!=_Go){return true;}else{if(_Gd>=_Gp){if(_Gd!=_Gp){return true;}else{if(_Ge>=_Gq){if(_Ge!=_Gq){return true;}else{var _Gt=E(_Gf),_Gu=E(_Gr);if(_Gt>=_Gu){if(_Gt!=_Gu){return true;}else{return new F(function(){return _bx(_Gg,_Gs);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_Gv=function(_Gw,_Gx){var _Gy=E(_Gw),_Gz=E(_Gy.a),_GA=E(_Gy.b),_GB=E(_Gy.c),_GC=E(_Gy.e),_GD=E(_Gx),_GE=E(_GD.a),_GF=E(_GD.b),_GG=E(_GD.c),_GH=E(_GD.e);return new F(function(){return _G4(_Gz.a,_Gz.b,_Gz.c,_GA.a,_GA.b,_GA.c,_GB.a,_GB.b,_GB.c,_Gy.d,_GC.a,_GC.b,_GE.a,_GE.b,_GE.c,_GF.a,_GF.b,_GF.c,_GG.a,_GG.b,_GG.c,_GD.d,_GH.a,_GH.b);});},_GI=function(_GJ,_GK,_GL,_GM,_GN,_GO){if(_GJ>=_GM){if(_GJ!=_GM){return true;}else{var _GP=E(_GK),_GQ=E(_GN),_GR=E(_GP.a),_GS=E(_GQ.a);if(_GR>=_GS){if(_GR!=_GS){return true;}else{var _GT=E(_GP.b),_GU=E(_GQ.b);if(_GT>=_GU){if(_GT!=_GU){return true;}else{var _GV=E(_GP.c),_GW=E(_GQ.c);if(_GV>=_GW){if(_GV!=_GW){return true;}else{return new F(function(){return _Gv(_GL,_GO);});}}else{return false;}}}else{return false;}}}else{return false;}}}else{return false;}},_GX=function(_GY,_GZ){var _H0=E(_GY),_H1=E(_GZ);return new F(function(){return _GI(E(_H0.a),_H0.b,_H0.c,E(_H1.a),_H1.b,_H1.c);});},_H2=function(_H3,_H4){var _H5=E(_H3),_H6=E(_H5.a),_H7=E(_H4),_H8=E(_H7.a);if(_H6>=_H8){if(_H6!=_H8){return E(_H5);}else{var _H9=E(_H5.b),_Ha=E(_H7.b),_Hb=E(_H9.a),_Hc=E(_Ha.a);if(_Hb>=_Hc){if(_Hb!=_Hc){return E(_H5);}else{var _Hd=E(_H9.b),_He=E(_Ha.b);if(_Hd>=_He){if(_Hd!=_He){return E(_H5);}else{var _Hf=E(_H9.c),_Hg=E(_Ha.c);if(_Hf>=_Hg){if(_Hf!=_Hg){return E(_H5);}else{var _Hh=E(_H5.c),_Hi=_Hh.d,_Hj=E(_Hh.a),_Hk=_Hj.a,_Hl=_Hj.b,_Hm=_Hj.c,_Hn=E(_Hh.b),_Ho=_Hn.a,_Hp=_Hn.b,_Hq=_Hn.c,_Hr=E(_Hh.c),_Hs=_Hr.a,_Ht=_Hr.b,_Hu=_Hr.c,_Hv=E(_Hh.e),_Hw=E(_H7.c),_Hx=_Hw.d,_Hy=E(_Hw.a),_Hz=_Hy.a,_HA=_Hy.b,_HB=_Hy.c,_HC=E(_Hw.b),_HD=_HC.a,_HE=_HC.b,_HF=_HC.c,_HG=E(_Hw.c),_HH=_HG.a,_HI=_HG.b,_HJ=_HG.c,_HK=E(_Hw.e);if(_Hk>=_Hz){if(_Hk!=_Hz){return E(_H5);}else{if(_Hl>=_HA){if(_Hl!=_HA){return E(_H5);}else{if(_Hm>=_HB){if(_Hm!=_HB){return E(_H5);}else{if(_Ho>=_HD){if(_Ho!=_HD){return E(_H5);}else{if(_Hp>=_HE){if(_Hp!=_HE){return E(_H5);}else{if(_Hq>=_HF){if(_Hq!=_HF){return E(_H5);}else{if(_Hs>=_HH){if(_Hs!=_HH){return E(_H5);}else{if(_Ht>=_HI){if(_Ht!=_HI){return E(_H5);}else{if(_Hu>=_HJ){if(_Hu!=_HJ){return E(_H5);}else{if(_Hi>=_Hx){if(_Hi!=_Hx){return E(_H5);}else{var _HL=E(_Hv.a),_HM=E(_HK.a);return (_HL>=_HM)?(_HL!=_HM)?E(_H5):(E(_Hv.b)>E(_HK.b))?E(_H5):E(_H7):E(_H7);}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}}}else{return E(_H7);}},_HN=function(_HO,_HP){var _HQ=E(_HO),_HR=E(_HQ.a),_HS=E(_HP),_HT=E(_HS.a);if(_HR>=_HT){if(_HR!=_HT){return E(_HS);}else{var _HU=E(_HQ.b),_HV=E(_HS.b),_HW=E(_HU.a),_HX=E(_HV.a);if(_HW>=_HX){if(_HW!=_HX){return E(_HS);}else{var _HY=E(_HU.b),_HZ=E(_HV.b);if(_HY>=_HZ){if(_HY!=_HZ){return E(_HS);}else{var _I0=E(_HU.c),_I1=E(_HV.c);if(_I0>=_I1){if(_I0!=_I1){return E(_HS);}else{var _I2=E(_HQ.c),_I3=_I2.d,_I4=E(_I2.a),_I5=_I4.a,_I6=_I4.b,_I7=_I4.c,_I8=E(_I2.b),_I9=_I8.a,_Ia=_I8.b,_Ib=_I8.c,_Ic=E(_I2.c),_Id=_Ic.a,_Ie=_Ic.b,_If=_Ic.c,_Ig=E(_I2.e),_Ih=E(_HS.c),_Ii=_Ih.d,_Ij=E(_Ih.a),_Ik=_Ij.a,_Il=_Ij.b,_Im=_Ij.c,_In=E(_Ih.b),_Io=_In.a,_Ip=_In.b,_Iq=_In.c,_Ir=E(_Ih.c),_Is=_Ir.a,_It=_Ir.b,_Iu=_Ir.c,_Iv=E(_Ih.e);if(_I5>=_Ik){if(_I5!=_Ik){return E(_HS);}else{if(_I6>=_Il){if(_I6!=_Il){return E(_HS);}else{if(_I7>=_Im){if(_I7!=_Im){return E(_HS);}else{if(_I9>=_Io){if(_I9!=_Io){return E(_HS);}else{if(_Ia>=_Ip){if(_Ia!=_Ip){return E(_HS);}else{if(_Ib>=_Iq){if(_Ib!=_Iq){return E(_HS);}else{if(_Id>=_Is){if(_Id!=_Is){return E(_HS);}else{if(_Ie>=_It){if(_Ie!=_It){return E(_HS);}else{if(_If>=_Iu){if(_If!=_Iu){return E(_HS);}else{if(_I3>=_Ii){if(_I3!=_Ii){return E(_HS);}else{var _Iw=E(_Ig.a),_Ix=E(_Iv.a);return (_Iw>=_Ix)?(_Iw!=_Ix)?E(_HS):(E(_Ig.b)>E(_Iv.b))?E(_HS):E(_HQ):E(_HQ);}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}}}else{return E(_HQ);}},_Iy={_:0,a:_Cb,b:_D5,c:_E3,d:_F1,e:_FZ,f:_GX,g:_H2,h:_HN},_Iz=function(_IA,_IB,_IC,_ID){var _IE=E(_ID);if(!_IE._){var _IF=_IE.c,_IG=_IE.d,_IH=_IE.e,_II=E(_IE.b),_IJ=E(_II.a);if(_IA>=_IJ){if(_IA!=_IJ){return new F(function(){return _xc(_II,_IF,_IG,B(_Iz(_IA,_IB,_IC,_IH)));});}else{var _IK=E(_II.b);if(_IB>=_IK){if(_IB!=_IK){return new F(function(){return _xc(_II,_IF,_IG,B(_Iz(_IA,_IB,_IC,_IH)));});}else{return new T5(0,_IE.a,E(new T2(0,_IA,_IB)),_IC,E(_IG),E(_IH));}}else{return new F(function(){return _wv(_II,_IF,B(_Iz(_IA,_IB,_IC,_IG)),_IH);});}}}else{return new F(function(){return _wv(_II,_IF,B(_Iz(_IA,_IB,_IC,_IG)),_IH);});}}else{return new T5(0,1,E(new T2(0,_IA,_IB)),_IC,E(_wq),E(_wq));}},_IL=new T0(1),_IM=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_IN=function(_IO){return new F(function(){return err(_IM);});},_IP=new T(function(){return B(_IN(_));}),_IQ=function(_IR,_IS,_IT){var _IU=E(_IT);if(!_IU._){var _IV=_IU.a,_IW=E(_IS);if(!_IW._){var _IX=_IW.a,_IY=_IW.b;if(_IX<=(imul(3,_IV)|0)){return new T4(0,(1+_IX|0)+_IV|0,E(_IR),E(_IW),E(_IU));}else{var _IZ=E(_IW.c);if(!_IZ._){var _J0=_IZ.a,_J1=E(_IW.d);if(!_J1._){var _J2=_J1.a,_J3=_J1.b,_J4=_J1.c;if(_J2>=(imul(2,_J0)|0)){var _J5=function(_J6){var _J7=E(_J1.d);return (_J7._==0)?new T4(0,(1+_IX|0)+_IV|0,E(_J3),E(new T4(0,(1+_J0|0)+_J6|0,E(_IY),E(_IZ),E(_J4))),E(new T4(0,(1+_IV|0)+_J7.a|0,E(_IR),E(_J7),E(_IU)))):new T4(0,(1+_IX|0)+_IV|0,E(_J3),E(new T4(0,(1+_J0|0)+_J6|0,E(_IY),E(_IZ),E(_J4))),E(new T4(0,1+_IV|0,E(_IR),E(_IL),E(_IU))));},_J8=E(_J4);if(!_J8._){return new F(function(){return _J5(_J8.a);});}else{return new F(function(){return _J5(0);});}}else{return new T4(0,(1+_IX|0)+_IV|0,E(_IY),E(_IZ),E(new T4(0,(1+_IV|0)+_J2|0,E(_IR),E(_J1),E(_IU))));}}else{return E(_IP);}}else{return E(_IP);}}}else{return new T4(0,1+_IV|0,E(_IR),E(_IL),E(_IU));}}else{var _J9=E(_IS);if(!_J9._){var _Ja=_J9.a,_Jb=_J9.b,_Jc=_J9.d,_Jd=E(_J9.c);if(!_Jd._){var _Je=_Jd.a,_Jf=E(_Jc);if(!_Jf._){var _Jg=_Jf.a,_Jh=_Jf.b,_Ji=_Jf.c;if(_Jg>=(imul(2,_Je)|0)){var _Jj=function(_Jk){var _Jl=E(_Jf.d);return (_Jl._==0)?new T4(0,1+_Ja|0,E(_Jh),E(new T4(0,(1+_Je|0)+_Jk|0,E(_Jb),E(_Jd),E(_Ji))),E(new T4(0,1+_Jl.a|0,E(_IR),E(_Jl),E(_IL)))):new T4(0,1+_Ja|0,E(_Jh),E(new T4(0,(1+_Je|0)+_Jk|0,E(_Jb),E(_Jd),E(_Ji))),E(new T4(0,1,E(_IR),E(_IL),E(_IL))));},_Jm=E(_Ji);if(!_Jm._){return new F(function(){return _Jj(_Jm.a);});}else{return new F(function(){return _Jj(0);});}}else{return new T4(0,1+_Ja|0,E(_Jb),E(_Jd),E(new T4(0,1+_Jg|0,E(_IR),E(_Jf),E(_IL))));}}else{return new T4(0,3,E(_Jb),E(_Jd),E(new T4(0,1,E(_IR),E(_IL),E(_IL))));}}else{var _Jn=E(_Jc);return (_Jn._==0)?new T4(0,3,E(_Jn.b),E(new T4(0,1,E(_Jb),E(_IL),E(_IL))),E(new T4(0,1,E(_IR),E(_IL),E(_IL)))):new T4(0,2,E(_IR),E(_J9),E(_IL));}}else{return new T4(0,1,E(_IR),E(_IL),E(_IL));}}},_Jo=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_Jp=function(_Jq){return new F(function(){return err(_Jo);});},_Jr=new T(function(){return B(_Jp(_));}),_Js=function(_Jt,_Ju,_Jv){var _Jw=E(_Ju);if(!_Jw._){var _Jx=_Jw.a,_Jy=E(_Jv);if(!_Jy._){var _Jz=_Jy.a,_JA=_Jy.b;if(_Jz<=(imul(3,_Jx)|0)){return new T4(0,(1+_Jx|0)+_Jz|0,E(_Jt),E(_Jw),E(_Jy));}else{var _JB=E(_Jy.c);if(!_JB._){var _JC=_JB.a,_JD=_JB.b,_JE=_JB.c,_JF=E(_Jy.d);if(!_JF._){var _JG=_JF.a;if(_JC>=(imul(2,_JG)|0)){var _JH=function(_JI){var _JJ=E(_Jt),_JK=E(_JB.d);return (_JK._==0)?new T4(0,(1+_Jx|0)+_Jz|0,E(_JD),E(new T4(0,(1+_Jx|0)+_JI|0,E(_JJ),E(_Jw),E(_JE))),E(new T4(0,(1+_JG|0)+_JK.a|0,E(_JA),E(_JK),E(_JF)))):new T4(0,(1+_Jx|0)+_Jz|0,E(_JD),E(new T4(0,(1+_Jx|0)+_JI|0,E(_JJ),E(_Jw),E(_JE))),E(new T4(0,1+_JG|0,E(_JA),E(_IL),E(_JF))));},_JL=E(_JE);if(!_JL._){return new F(function(){return _JH(_JL.a);});}else{return new F(function(){return _JH(0);});}}else{return new T4(0,(1+_Jx|0)+_Jz|0,E(_JA),E(new T4(0,(1+_Jx|0)+_JC|0,E(_Jt),E(_Jw),E(_JB))),E(_JF));}}else{return E(_Jr);}}else{return E(_Jr);}}}else{return new T4(0,1+_Jx|0,E(_Jt),E(_Jw),E(_IL));}}else{var _JM=E(_Jv);if(!_JM._){var _JN=_JM.a,_JO=_JM.b,_JP=_JM.d,_JQ=E(_JM.c);if(!_JQ._){var _JR=_JQ.a,_JS=_JQ.b,_JT=_JQ.c,_JU=E(_JP);if(!_JU._){var _JV=_JU.a;if(_JR>=(imul(2,_JV)|0)){var _JW=function(_JX){var _JY=E(_Jt),_JZ=E(_JQ.d);return (_JZ._==0)?new T4(0,1+_JN|0,E(_JS),E(new T4(0,1+_JX|0,E(_JY),E(_IL),E(_JT))),E(new T4(0,(1+_JV|0)+_JZ.a|0,E(_JO),E(_JZ),E(_JU)))):new T4(0,1+_JN|0,E(_JS),E(new T4(0,1+_JX|0,E(_JY),E(_IL),E(_JT))),E(new T4(0,1+_JV|0,E(_JO),E(_IL),E(_JU))));},_K0=E(_JT);if(!_K0._){return new F(function(){return _JW(_K0.a);});}else{return new F(function(){return _JW(0);});}}else{return new T4(0,1+_JN|0,E(_JO),E(new T4(0,1+_JR|0,E(_Jt),E(_IL),E(_JQ))),E(_JU));}}else{return new T4(0,3,E(_JS),E(new T4(0,1,E(_Jt),E(_IL),E(_IL))),E(new T4(0,1,E(_JO),E(_IL),E(_IL))));}}else{var _K1=E(_JP);return (_K1._==0)?new T4(0,3,E(_JO),E(new T4(0,1,E(_Jt),E(_IL),E(_IL))),E(_K1)):new T4(0,2,E(_Jt),E(_IL),E(_JM));}}else{return new T4(0,1,E(_Jt),E(_IL),E(_IL));}}},_K2=function(_K3,_K4,_K5){var _K6=E(_K4),_K7=E(_K5);if(!_K7._){var _K8=_K7.b,_K9=_K7.c,_Ka=_K7.d;switch(B(A3(_wo,_K3,_K6,_K8))){case 0:return new F(function(){return _IQ(_K8,B(_K2(_K3,_K6,_K9)),_Ka);});break;case 1:return new T4(0,_K7.a,E(_K6),E(_K9),E(_Ka));default:return new F(function(){return _Js(_K8,_K9,B(_K2(_K3,_K6,_Ka)));});}}else{return new T4(0,1,E(_K6),E(_IL),E(_IL));}},_Kb=function(_Kc,_Kd,_Ke,_Kf,_Kg){var _Kh=E(_Kg);if(!_Kh._){var _Ki=new T(function(){var _Kj=B(_Kb(_Kh.a,_Kh.b,_Kh.c,_Kh.d,_Kh.e));return new T2(0,_Kj.a,_Kj.b);});return new T2(0,new T(function(){return E(E(_Ki).a);}),new T(function(){return B(_wv(_Kd,_Ke,_Kf,E(_Ki).b));}));}else{return new T2(0,new T2(0,_Kd,_Ke),_Kf);}},_Kk=function(_Kl,_Km,_Kn,_Ko,_Kp){var _Kq=E(_Ko);if(!_Kq._){var _Kr=new T(function(){var _Ks=B(_Kk(_Kq.a,_Kq.b,_Kq.c,_Kq.d,_Kq.e));return new T2(0,_Ks.a,_Ks.b);});return new T2(0,new T(function(){return E(E(_Kr).a);}),new T(function(){return B(_xc(_Km,_Kn,E(_Kr).b,_Kp));}));}else{return new T2(0,new T2(0,_Km,_Kn),_Kp);}},_Kt=function(_Ku,_Kv){var _Kw=E(_Ku);if(!_Kw._){var _Kx=_Kw.a,_Ky=E(_Kv);if(!_Ky._){var _Kz=_Ky.a;if(_Kx<=_Kz){var _KA=B(_Kk(_Kz,_Ky.b,_Ky.c,_Ky.d,_Ky.e)),_KB=E(_KA.a);return new F(function(){return _wv(_KB.a,_KB.b,_Kw,_KA.b);});}else{var _KC=B(_Kb(_Kx,_Kw.b,_Kw.c,_Kw.d,_Kw.e)),_KD=E(_KC.a);return new F(function(){return _xc(_KD.a,_KD.b,_KC.b,_Ky);});}}else{return E(_Kw);}}else{return E(_Kv);}},_KE=function(_KF,_KG,_KH,_KI){var _KJ=E(_KI);if(!_KJ._){var _KK=_KJ.c,_KL=_KJ.d,_KM=_KJ.e,_KN=E(_KJ.b),_KO=E(_KN.a);if(_KG>=_KO){if(_KG!=_KO){return new F(function(){return _wv(_KN,_KK,_KL,B(_KE(_KF,_KG,_KH,_KM)));});}else{var _KP=E(_KN.b);if(_KH>=_KP){if(_KH!=_KP){return new F(function(){return _wv(_KN,_KK,_KL,B(_KE(_KF,_KG,_KH,_KM)));});}else{var _KQ=B(A2(_KF,_KN,_KK));if(!_KQ._){return new F(function(){return _Kt(_KL,_KM);});}else{return new T5(0,_KJ.a,E(_KN),_KQ.a,E(_KL),E(_KM));}}}else{return new F(function(){return _xc(_KN,_KK,B(_KE(_KF,_KG,_KH,_KL)),_KM);});}}}else{return new F(function(){return _xc(_KN,_KK,B(_KE(_KF,_KG,_KH,_KL)),_KM);});}}else{return new T0(1);}},_KR=function(_KS,_KT,_KU,_KV){var _KW=E(_KV);if(!_KW._){var _KX=_KW.c,_KY=_KW.d,_KZ=_KW.e,_L0=E(_KW.b),_L1=E(_L0.a);if(_KT>=_L1){if(_KT!=_L1){return new F(function(){return _wv(_L0,_KX,_KY,B(_KR(_KS,_KT,_KU,_KZ)));});}else{var _L2=E(_KU),_L3=E(_L0.b);if(_L2>=_L3){if(_L2!=_L3){return new F(function(){return _wv(_L0,_KX,_KY,B(_KE(_KS,_KT,_L2,_KZ)));});}else{var _L4=B(A2(_KS,_L0,_KX));if(!_L4._){return new F(function(){return _Kt(_KY,_KZ);});}else{return new T5(0,_KW.a,E(_L0),_L4.a,E(_KY),E(_KZ));}}}else{return new F(function(){return _xc(_L0,_KX,B(_KE(_KS,_KT,_L2,_KY)),_KZ);});}}}else{return new F(function(){return _xc(_L0,_KX,B(_KR(_KS,_KT,_KU,_KY)),_KZ);});}}else{return new T0(1);}},_L5=function(_L6,_L7,_L8,_L9){var _La=E(_L9);if(!_La._){var _Lb=_La.c,_Lc=_La.d,_Ld=_La.e,_Le=E(_La.b),_Lf=E(_L7),_Lg=E(_Le.a);if(_Lf>=_Lg){if(_Lf!=_Lg){return new F(function(){return _wv(_Le,_Lb,_Lc,B(_KR(_L6,_Lf,_L8,_Ld)));});}else{var _Lh=E(_L8),_Li=E(_Le.b);if(_Lh>=_Li){if(_Lh!=_Li){return new F(function(){return _wv(_Le,_Lb,_Lc,B(_KE(_L6,_Lf,_Lh,_Ld)));});}else{var _Lj=B(A2(_L6,_Le,_Lb));if(!_Lj._){return new F(function(){return _Kt(_Lc,_Ld);});}else{return new T5(0,_La.a,E(_Le),_Lj.a,E(_Lc),E(_Ld));}}}else{return new F(function(){return _xc(_Le,_Lb,B(_KE(_L6,_Lf,_Lh,_Lc)),_Ld);});}}}else{return new F(function(){return _xc(_Le,_Lb,B(_KR(_L6,_Lf,_L8,_Lc)),_Ld);});}}else{return new T0(1);}},_Lk=function(_Ll,_Lm,_Ln,_Lo,_Lp,_Lq,_Lr,_Ls,_Lt,_Lu){var _Lv=_Lt-_Ln,_Lw=_Lu-_Lo,_Lx=_Lq-_Ln,_Ly=_Lr-_Lo,_Lz=_Lx*_Lw-_Ly*_Lv+(_Lx*_Lw-_Ly*_Lv);return (_Lz>0)?new T1(1,new T(function(){var _LA=_Lv*_Lv+_Lw*_Lw,_LB=_Lx*_Lx+_Ly*_Ly,_LC=E(_Ll),_LD=_Ln+(_Lw*_LB-_Ly*_LA)/_Lz,_LE=_Lo+(_Lx*_LA-_Lv*_LB)/_Lz,_LF=_LE+Math.sqrt((_LD-_Ln)*(_LD-_Ln)+(_LE-_Lo)*(_LE-_Lo));if(_LF>_LC){return new T5(0,E(new T3(0,_Lm,_Ln,_Lo)),E(new T3(0,_Lp,_Lq,_Lr)),E(new T3(0,_Ls,_Lt,_Lu)),_LC,E(new T2(0,_LD,_LE)));}else{return new T5(0,E(new T3(0,_Lm,_Ln,_Lo)),E(new T3(0,_Lp,_Lq,_Lr)),E(new T3(0,_Ls,_Lt,_Lu)),_LF,E(new T2(0,_LD,_LE)));}})):__Z;},_LG=function(_LH,_LI,_LJ){while(1){var _LK=E(_LH);if(!_LK._){return E(_LI);}else{_LH=_LK.a;_LI=_LK.b;_LJ=_LK.c;continue;}}},_LL=function(_LM,_LN,_LO){var _LP=E(_LM);return (_LP._==0)?E(_LO):new T3(1,new T(function(){return B(_LL(_LP.a,_LP.b,_LP.c));}),_LN,_LO);},_LQ=new T(function(){return B(_84("Fortune/BreakpointTree.hs:(154,1)-(163,30)|function delete"));}),_LR=new T(function(){return B(unCStr("delete: Reached Nil"));}),_LS=new T(function(){return B(err(_LR));}),_LT=function(_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M1){var _M2=E(_M1);if(!_M2._){return E(_LS);}else{var _M3=_M2.a,_M4=_M2.c,_M5=E(_M2.b),_M6=E(_M5.a),_M7=_M6.b,_M8=_M6.c,_M9=E(_M5.b),_Ma=_M9.b,_Mb=_M9.c,_Mc=function(_Md){var _Me=_LW-_LZ,_Mf=function(_Mg){var _Mh=_M8-_Mb,_Mi=function(_Mj){return (_Mg>=_Mj)?(_Mg<_Mj)?E(_LQ):new T3(1,_M3,_M5,new T(function(){return B(_LT(_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M4));})):new T3(1,new T(function(){return B(_LT(_LU,_LV,_LW,_LX,_LY,_LZ,_M0,_M3));}),_M5,_M4);};if(_Mh!=0){if(_Mh<=0){if( -_Mh>=1.0e-7){var _Mk=E(_M0);return new F(function(){return _Mi((_M8*_Ma+Math.sqrt(((_M7-_Ma)*(_M7-_Ma)+_Mh*_Mh)*(_M8-_Mk)*(_Mb-_Mk))+(_M7*(_Mk-_Mb)-_Ma*_Mk))/_Mh);});}else{return new F(function(){return _Mi((_M7+_Ma)/2);});}}else{if(_Mh>=1.0e-7){var _Ml=E(_M0);return new F(function(){return _Mi((_M8*_Ma+Math.sqrt(((_M7-_Ma)*(_M7-_Ma)+_Mh*_Mh)*(_M8-_Ml)*(_Mb-_Ml))+(_M7*(_Ml-_Mb)-_Ma*_Ml))/_Mh);});}else{return new F(function(){return _Mi((_M7+_Ma)/2);});}}}else{return new F(function(){return _Mi((_M7+_Ma)/2);});}};if(_Me!=0){if(_Me<=0){if( -_Me>=1.0e-7){var _Mm=E(_M0);return new F(function(){return _Mf((_LW*_LY+Math.sqrt(((_LV-_LY)*(_LV-_LY)+_Me*_Me)*(_LW-_Mm)*(_LZ-_Mm))+(_LV*(_Mm-_LZ)-_LY*_Mm))/_Me);});}else{return new F(function(){return _Mf((_LV+_LY)/2);});}}else{if(_Me>=1.0e-7){var _Mn=E(_M0);return new F(function(){return _Mf((_LW*_LY+Math.sqrt(((_LV-_LY)*(_LV-_LY)+_Me*_Me)*(_LW-_Mn)*(_LZ-_Mn))+(_LV*(_Mn-_LZ)-_LY*_Mn))/_Me);});}else{return new F(function(){return _Mf((_LV+_LY)/2);});}}}else{return new F(function(){return _Mf((_LV+_LY)/2);});}};if(_M6.a!=_LU){return new F(function(){return _Mc(_);});}else{if(_M9.a!=_LX){return new F(function(){return _Mc(_);});}else{var _Mo=E(_M3);if(!_Mo._){return E(_M4);}else{var _Mp=E(_M4);if(!_Mp._){return E(_Mo);}else{var _Mq=_Mp.a,_Mr=_Mp.b,_Ms=_Mp.c;return new T3(1,_Mo,new T(function(){return B(_LG(_Mq,_Mr,_Ms));}),new T(function(){return B(_LL(_Mq,_Mr,_Ms));}));}}}}}},_Mt=function(_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB,_MC,_MD){var _ME=E(_MC),_MF=E(_ME.a),_MG=_MF.b,_MH=_MF.c,_MI=E(_ME.b),_MJ=_MI.b,_MK=_MI.c,_ML=function(_MM){var _MN=_Mw-_Mz,_MO=function(_MP){var _MQ=_MH-_MK,_MR=function(_MS){return (_MP>=_MS)?(_MP<_MS)?E(_LQ):new T3(1,_MB,_ME,new T(function(){return B(_LT(_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MD));})):new T3(1,new T(function(){return B(_LT(_Mu,_Mv,_Mw,_Mx,_My,_Mz,_MA,_MB));}),_ME,_MD);};if(_MQ!=0){if(_MQ<=0){if( -_MQ>=1.0e-7){var _MT=E(_MA);return new F(function(){return _MR((_MH*_MJ+Math.sqrt(((_MG-_MJ)*(_MG-_MJ)+_MQ*_MQ)*(_MH-_MT)*(_MK-_MT))+(_MG*(_MT-_MK)-_MJ*_MT))/_MQ);});}else{return new F(function(){return _MR((_MG+_MJ)/2);});}}else{if(_MQ>=1.0e-7){var _MU=E(_MA);return new F(function(){return _MR((_MH*_MJ+Math.sqrt(((_MG-_MJ)*(_MG-_MJ)+_MQ*_MQ)*(_MH-_MU)*(_MK-_MU))+(_MG*(_MU-_MK)-_MJ*_MU))/_MQ);});}else{return new F(function(){return _MR((_MG+_MJ)/2);});}}}else{return new F(function(){return _MR((_MG+_MJ)/2);});}};if(_MN!=0){if(_MN<=0){if( -_MN>=1.0e-7){var _MV=E(_MA);return new F(function(){return _MO((_Mw*_My+Math.sqrt(((_Mv-_My)*(_Mv-_My)+_MN*_MN)*(_Mw-_MV)*(_Mz-_MV))+(_Mv*(_MV-_Mz)-_My*_MV))/_MN);});}else{return new F(function(){return _MO((_Mv+_My)/2);});}}else{if(_MN>=1.0e-7){var _MW=E(_MA);return new F(function(){return _MO((_Mw*_My+Math.sqrt(((_Mv-_My)*(_Mv-_My)+_MN*_MN)*(_Mw-_MW)*(_Mz-_MW))+(_Mv*(_MW-_Mz)-_My*_MW))/_MN);});}else{return new F(function(){return _MO((_Mv+_My)/2);});}}}else{return new F(function(){return _MO((_Mv+_My)/2);});}};if(_MF.a!=_Mu){return new F(function(){return _ML(_);});}else{if(_MI.a!=_Mx){return new F(function(){return _ML(_);});}else{var _MX=E(_MB);if(!_MX._){return E(_MD);}else{var _MY=E(_MD);if(!_MY._){return E(_MX);}else{var _MZ=_MY.a,_N0=_MY.b,_N1=_MY.c;return new T3(1,_MX,new T(function(){return B(_LG(_MZ,_N0,_N1));}),new T(function(){return B(_LL(_MZ,_N0,_N1));}));}}}}},_N2=function(_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc,_Nd,_Ne){var _Nf=E(_Nd),_Ng=E(_Nf.a),_Nh=_Ng.b,_Ni=_Ng.c,_Nj=E(_Nf.b),_Nk=_Nj.b,_Nl=_Nj.c,_Nm=function(_Nn){var _No=_N5-_N8,_Np=function(_Nq){var _Nr=_Ni-_Nl,_Ns=function(_Nt){return (_Nq>=_Nt)?(_Nq<_Nt)?E(_LQ):new T3(1,new T3(1,_Na,_Nb,_Nc),_Nf,new T(function(){return B(_LT(_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Ne));})):new T3(1,new T(function(){return B(_Mt(_N3,_N4,_N5,_N6,_N7,_N8,_N9,_Na,_Nb,_Nc));}),_Nf,_Ne);};if(_Nr!=0){if(_Nr<=0){if( -_Nr>=1.0e-7){var _Nu=E(_N9);return new F(function(){return _Ns((_Ni*_Nk+Math.sqrt(((_Nh-_Nk)*(_Nh-_Nk)+_Nr*_Nr)*(_Ni-_Nu)*(_Nl-_Nu))+(_Nh*(_Nu-_Nl)-_Nk*_Nu))/_Nr);});}else{return new F(function(){return _Ns((_Nh+_Nk)/2);});}}else{if(_Nr>=1.0e-7){var _Nv=E(_N9);return new F(function(){return _Ns((_Ni*_Nk+Math.sqrt(((_Nh-_Nk)*(_Nh-_Nk)+_Nr*_Nr)*(_Ni-_Nv)*(_Nl-_Nv))+(_Nh*(_Nv-_Nl)-_Nk*_Nv))/_Nr);});}else{return new F(function(){return _Ns((_Nh+_Nk)/2);});}}}else{return new F(function(){return _Ns((_Nh+_Nk)/2);});}};if(_No!=0){if(_No<=0){if( -_No>=1.0e-7){var _Nw=E(_N9);return new F(function(){return _Np((_N5*_N7+Math.sqrt(((_N4-_N7)*(_N4-_N7)+_No*_No)*(_N5-_Nw)*(_N8-_Nw))+(_N4*(_Nw-_N8)-_N7*_Nw))/_No);});}else{return new F(function(){return _Np((_N4+_N7)/2);});}}else{if(_No>=1.0e-7){var _Nx=E(_N9);return new F(function(){return _Np((_N5*_N7+Math.sqrt(((_N4-_N7)*(_N4-_N7)+_No*_No)*(_N5-_Nx)*(_N8-_Nx))+(_N4*(_Nx-_N8)-_N7*_Nx))/_No);});}else{return new F(function(){return _Np((_N4+_N7)/2);});}}}else{return new F(function(){return _Np((_N4+_N7)/2);});}};if(_Ng.a!=_N3){return new F(function(){return _Nm(_);});}else{if(_Nj.a!=_N6){return new F(function(){return _Nm(_);});}else{var _Ny=E(_Ne);if(!_Ny._){return new T3(1,_Na,_Nb,_Nc);}else{var _Nz=_Ny.a,_NA=_Ny.b,_NB=_Ny.c;return new T3(1,new T3(1,_Na,_Nb,_Nc),new T(function(){return B(_LG(_Nz,_NA,_NB));}),new T(function(){return B(_LL(_Nz,_NA,_NB));}));}}}},_NC=function(_ND,_NE,_NF,_NG,_NH){var _NI=_NE-_NG;if(_NI!=0){if(_NI<=0){if( -_NI>=1.0e-7){var _NJ=E(_NH);return (_NE*_NF+Math.sqrt(((_ND-_NF)*(_ND-_NF)+_NI*_NI)*(_NE-_NJ)*(_NG-_NJ))+(_ND*(_NJ-_NG)-_NF*_NJ))/_NI;}else{return (_ND+_NF)/2;}}else{if(_NI>=1.0e-7){var _NK=E(_NH);return (_NE*_NF+Math.sqrt(((_ND-_NF)*(_ND-_NF)+_NI*_NI)*(_NE-_NK)*(_NG-_NK))+(_ND*(_NK-_NG)-_NF*_NK))/_NI;}else{return (_ND+_NF)/2;}}}else{return (_ND+_NF)/2;}},_NL=new T(function(){return B(unCStr("delete2: reached nil."));}),_NM=new T(function(){return B(err(_NL));}),_NN=function(_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O1){var _O2=E(_O1);if(!_O2._){return E(_NM);}else{var _O3=_O2.a,_O4=_O2.c,_O5=E(_O2.b),_O6=E(_O5.a),_O7=_O6.a,_O8=_O6.b,_O9=_O6.c,_Oa=E(_O5.b),_Ob=_Oa.a,_Oc=_Oa.b,_Od=_Oa.c,_Oe=function(_Of){var _Og=function(_Oh){var _Oi=_NQ-_NT,_Oj=function(_Ok){var _Ol=_O9-_Od,_Om=function(_On){var _Oo=new T(function(){return B(_NC(_NV,_NW,_NY,_NZ,_O0));}),_Op=function(_Oq){var _Or=function(_Os){return (_Ok>=_On)?new T3(1,new T(function(){return B(_LT(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O3));}),_O5,new T(function(){return B(_LT(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_O4));})):new T3(1,new T(function(){return B(_LT(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_O3));}),_O5,new T(function(){return B(_LT(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O4));}));};if(_Ok<_On){return new F(function(){return _Or(_);});}else{if(E(_Oo)<_On){return new F(function(){return _Or(_);});}else{return new T3(1,_O3,_O5,new T(function(){return B(_NN(_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O4));}));}}};if(_Ok>=_On){return new F(function(){return _Op(_);});}else{if(E(_Oo)>=_On){return new F(function(){return _Op(_);});}else{return new T3(1,new T(function(){return B(_NN(_NO,_NP,_NQ,_NR,_NS,_NT,_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O3));}),_O5,_O4);}}};if(_Ol!=0){if(_Ol<=0){if( -_Ol>=1.0e-7){var _Ot=E(_O0);return new F(function(){return _Om((_O9*_Oc+Math.sqrt(((_O8-_Oc)*(_O8-_Oc)+_Ol*_Ol)*(_O9-_Ot)*(_Od-_Ot))+(_O8*(_Ot-_Od)-_Oc*_Ot))/_Ol);});}else{return new F(function(){return _Om((_O8+_Oc)/2);});}}else{if(_Ol>=1.0e-7){var _Ou=E(_O0);return new F(function(){return _Om((_O9*_Oc+Math.sqrt(((_O8-_Oc)*(_O8-_Oc)+_Ol*_Ol)*(_O9-_Ou)*(_Od-_Ou))+(_O8*(_Ou-_Od)-_Oc*_Ou))/_Ol);});}else{return new F(function(){return _Om((_O8+_Oc)/2);});}}}else{return new F(function(){return _Om((_O8+_Oc)/2);});}};if(_Oi!=0){if(_Oi<=0){if( -_Oi>=1.0e-7){var _Ov=E(_O0);return new F(function(){return _Oj((_NQ*_NS+Math.sqrt(((_NP-_NS)*(_NP-_NS)+_Oi*_Oi)*(_NQ-_Ov)*(_NT-_Ov))+(_NP*(_Ov-_NT)-_NS*_Ov))/_Oi);});}else{return new F(function(){return _Oj((_NP+_NS)/2);});}}else{if(_Oi>=1.0e-7){var _Ow=E(_O0);return new F(function(){return _Oj((_NQ*_NS+Math.sqrt(((_NP-_NS)*(_NP-_NS)+_Oi*_Oi)*(_NQ-_Ow)*(_NT-_Ow))+(_NP*(_Ow-_NT)-_NS*_Ow))/_Oi);});}else{return new F(function(){return _Oj((_NP+_NS)/2);});}}}else{return new F(function(){return _Oj((_NP+_NS)/2);});}};if(_NU!=_O7){return new F(function(){return _Og(_);});}else{if(_NX!=_Ob){return new F(function(){return _Og(_);});}else{var _Ox=E(_O3);if(!_Ox._){return new F(function(){return _LT(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_O4);});}else{var _Oy=_Ox.a,_Oz=_Ox.b,_OA=_Ox.c,_OB=E(_O4);if(!_OB._){return new F(function(){return _Mt(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_Oy,_Oz,_OA);});}else{var _OC=_OB.a,_OD=_OB.b,_OE=_OB.c;return new F(function(){return _N2(_NO,_NP,_NQ,_NR,_NS,_NT,_O0,_Oy,_Oz,_OA,new T(function(){return B(_LG(_OC,_OD,_OE));}),new T(function(){return B(_LL(_OC,_OD,_OE));}));});}}}}};if(_NO!=_O7){return new F(function(){return _Oe(_);});}else{if(_NR!=_Ob){return new F(function(){return _Oe(_);});}else{var _OF=E(_O3);if(!_OF._){return new F(function(){return _LT(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_O4);});}else{var _OG=_OF.a,_OH=_OF.b,_OI=_OF.c,_OJ=E(_O4);if(!_OJ._){return new F(function(){return _Mt(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_OG,_OH,_OI);});}else{var _OK=_OJ.a,_OL=_OJ.b,_OM=_OJ.c;return new F(function(){return _N2(_NU,_NV,_NW,_NX,_NY,_NZ,_O0,_OG,_OH,_OI,new T(function(){return B(_LG(_OK,_OL,_OM));}),new T(function(){return B(_LL(_OK,_OL,_OM));}));});}}}}}},_ON=__Z,_OO=new T(function(){return B(unCStr("insertPar: Cannot insert into empty tree."));}),_OP=new T(function(){return B(err(_OO));}),_OQ=function(_OR,_OS,_OT,_OU,_OV){var _OW=E(_OV);if(!_OW._){return E(_OP);}else{var _OX=_OW.b,_OY=_OW.c,_OZ=new T3(0,_OR,_OS,_OT),_P0=E(_OW.a);if(!_P0._){var _P1=E(_OY);if(!_P1._){var _P2=E(_OX),_P3=E(_P2.a),_P4=_P3.b,_P5=_P3.c,_P6=E(_P2.b),_P7=_P6.b,_P8=_P6.c,_P9=_P5-_P8,_Pa=function(_Pb){return (_OS>=_Pb)?new T2(0,new T3(1,_ON,_P2,new T3(1,_ON,new T2(0,E(_P6),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_P6)),_ON))),new T1(1,_P2)):new T2(0,new T3(1,new T3(1,_ON,new T2(0,E(_P3),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_P3)),_ON)),_P2,_ON),new T1(0,_P2));};if(_P9!=0){if(_P9<=0){if( -_P9>=1.0e-7){var _Pc=E(_OU);return new F(function(){return _Pa((_P5*_P7+Math.sqrt(((_P4-_P7)*(_P4-_P7)+_P9*_P9)*(_P5-_Pc)*(_P8-_Pc))+(_P4*(_Pc-_P8)-_P7*_Pc))/_P9);});}else{return new F(function(){return _Pa((_P4+_P7)/2);});}}else{if(_P9>=1.0e-7){var _Pd=E(_OU);return new F(function(){return _Pa((_P5*_P7+Math.sqrt(((_P4-_P7)*(_P4-_P7)+_P9*_P9)*(_P5-_Pd)*(_P8-_Pd))+(_P4*(_Pd-_P8)-_P7*_Pd))/_P9);});}else{return new F(function(){return _Pa((_P4+_P7)/2);});}}}else{return new F(function(){return _Pa((_P4+_P7)/2);});}}else{var _Pe=E(_OX),_Pf=E(_Pe.a),_Pg=_Pf.b,_Ph=_Pf.c,_Pi=E(_Pe.b),_Pj=_Pi.b,_Pk=_Pi.c,_Pl=_Ph-_Pk,_Pm=function(_Pn){if(_OS>=_Pn){var _Po=new T(function(){var _Pp=B(_OQ(_OR,_OS,_OT,_OU,_P1));return new T2(0,_Pp.a,_Pp.b);});return new T2(0,new T3(1,_ON,_Pe,new T(function(){return E(E(_Po).a);})),new T(function(){return E(E(_Po).b);}));}else{return new T2(0,new T3(1,new T3(1,_ON,new T2(0,E(_Pf),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_Pf)),_ON)),_Pe,_P1),new T1(0,_Pe));}};if(_Pl!=0){if(_Pl<=0){if( -_Pl>=1.0e-7){var _Pq=E(_OU);return new F(function(){return _Pm((_Ph*_Pj+Math.sqrt(((_Pg-_Pj)*(_Pg-_Pj)+_Pl*_Pl)*(_Ph-_Pq)*(_Pk-_Pq))+(_Pg*(_Pq-_Pk)-_Pj*_Pq))/_Pl);});}else{return new F(function(){return _Pm((_Pg+_Pj)/2);});}}else{if(_Pl>=1.0e-7){var _Pr=E(_OU);return new F(function(){return _Pm((_Ph*_Pj+Math.sqrt(((_Pg-_Pj)*(_Pg-_Pj)+_Pl*_Pl)*(_Ph-_Pr)*(_Pk-_Pr))+(_Pg*(_Pr-_Pk)-_Pj*_Pr))/_Pl);});}else{return new F(function(){return _Pm((_Pg+_Pj)/2);});}}}else{return new F(function(){return _Pm((_Pg+_Pj)/2);});}}}else{var _Ps=E(_OY);if(!_Ps._){var _Pt=E(_OX),_Pu=E(_Pt.b),_Pv=_Pu.b,_Pw=_Pu.c,_Px=E(_Pt.a),_Py=_Px.b,_Pz=_Px.c,_PA=_Pz-_Pw,_PB=function(_PC){if(_OS>=_PC){return new T2(0,new T3(1,_P0,_Pt,new T3(1,_ON,new T2(0,E(_Pu),E(_OZ)),new T3(1,_ON,new T2(0,E(_OZ),E(_Pu)),_ON))),new T1(1,_Pt));}else{var _PD=new T(function(){var _PE=B(_OQ(_OR,_OS,_OT,_OU,_P0));return new T2(0,_PE.a,_PE.b);});return new T2(0,new T3(1,new T(function(){return E(E(_PD).a);}),_Pt,_ON),new T(function(){return E(E(_PD).b);}));}};if(_PA!=0){if(_PA<=0){if( -_PA>=1.0e-7){var _PF=E(_OU);return new F(function(){return _PB((_Pz*_Pv+Math.sqrt(((_Py-_Pv)*(_Py-_Pv)+_PA*_PA)*(_Pz-_PF)*(_Pw-_PF))+(_Py*(_PF-_Pw)-_Pv*_PF))/_PA);});}else{return new F(function(){return _PB((_Py+_Pv)/2);});}}else{if(_PA>=1.0e-7){var _PG=E(_OU);return new F(function(){return _PB((_Pz*_Pv+Math.sqrt(((_Py-_Pv)*(_Py-_Pv)+_PA*_PA)*(_Pz-_PG)*(_Pw-_PG))+(_Py*(_PG-_Pw)-_Pv*_PG))/_PA);});}else{return new F(function(){return _PB((_Py+_Pv)/2);});}}}else{return new F(function(){return _PB((_Py+_Pv)/2);});}}else{var _PH=E(_OX),_PI=E(_PH.a),_PJ=_PI.b,_PK=_PI.c,_PL=E(_PH.b),_PM=_PL.b,_PN=_PL.c,_PO=_PK-_PN,_PP=function(_PQ){if(_OS>=_PQ){var _PR=new T(function(){var _PS=B(_OQ(_OR,_OS,_OT,_OU,_Ps));return new T2(0,_PS.a,_PS.b);});return new T2(0,new T3(1,_P0,_PH,new T(function(){return E(E(_PR).a);})),new T(function(){return E(E(_PR).b);}));}else{var _PT=new T(function(){var _PU=B(_OQ(_OR,_OS,_OT,_OU,_P0));return new T2(0,_PU.a,_PU.b);});return new T2(0,new T3(1,new T(function(){return E(E(_PT).a);}),_PH,_Ps),new T(function(){return E(E(_PT).b);}));}};if(_PO!=0){if(_PO<=0){if( -_PO>=1.0e-7){var _PV=E(_OU);return new F(function(){return _PP((_PK*_PM+Math.sqrt(((_PJ-_PM)*(_PJ-_PM)+_PO*_PO)*(_PK-_PV)*(_PN-_PV))+(_PJ*(_PV-_PN)-_PM*_PV))/_PO);});}else{return new F(function(){return _PP((_PJ+_PM)/2);});}}else{if(_PO>=1.0e-7){var _PW=E(_OU);return new F(function(){return _PP((_PK*_PM+Math.sqrt(((_PJ-_PM)*(_PJ-_PM)+_PO*_PO)*(_PK-_PW)*(_PN-_PW))+(_PJ*(_PW-_PN)-_PM*_PW))/_PO);});}else{return new F(function(){return _PP((_PJ+_PM)/2);});}}}else{return new F(function(){return _PP((_PJ+_PM)/2);});}}}}},_PX=function(_PY,_PZ){var _Q0=E(_PZ);if(!_Q0._){return __Z;}else{var _Q1=_Q0.a,_Q2=E(_PY);return (_Q2==1)?new T2(1,_Q1,_6):new T2(1,_Q1,new T(function(){return B(_PX(_Q2-1|0,_Q0.b));}));}},_Q3=__Z,_Q4=function(_Q5){while(1){var _Q6=B((function(_Q7){var _Q8=E(_Q7);if(!_Q8._){return __Z;}else{var _Q9=_Q8.b,_Qa=E(_Q8.a);if(!_Qa._){_Q5=_Q9;return __continue;}else{return new T2(1,_Qa.a,new T(function(){return B(_Q4(_Q9));}));}}})(_Q5));if(_Q6!=__continue){return _Q6;}}},_Qb=function(_Qc,_Qd,_Qe,_Qf){var _Qg=E(_Qd),_Qh=E(_Qe),_Qi=E(_Qf);return new F(function(){return _Lk(_Qc,_Qg.a,_Qg.b,_Qg.c,_Qh.a,_Qh.b,_Qh.c,_Qi.a,_Qi.b,_Qi.c);});},_Qj=function(_Qk,_Ql,_Qm){while(1){var _Qn=E(_Qm);if(!_Qn._){return false;}else{if(!B(A3(_jA,_Qk,_Ql,_Qn.a))){_Qm=_Qn.b;continue;}else{return true;}}}},_Qo=function(_Qp){return new T4(0,1,E(_Qp),E(_IL),E(_IL));},_Qq=function(_Qr,_Qs){var _Qt=E(_Qs);if(!_Qt._){return new F(function(){return _IQ(_Qt.b,B(_Qq(_Qr,_Qt.c)),_Qt.d);});}else{return new F(function(){return _Qo(_Qr);});}},_Qu=function(_Qv,_Qw){var _Qx=E(_Qw);if(!_Qx._){return new F(function(){return _Js(_Qx.b,_Qx.c,B(_Qu(_Qv,_Qx.d)));});}else{return new F(function(){return _Qo(_Qv);});}},_Qy=function(_Qz,_QA,_QB,_QC,_QD){return new F(function(){return _Js(_QB,_QC,B(_Qu(_Qz,_QD)));});},_QE=function(_QF,_QG,_QH,_QI,_QJ){return new F(function(){return _IQ(_QH,B(_Qq(_QF,_QI)),_QJ);});},_QK=function(_QL,_QM,_QN,_QO,_QP,_QQ){var _QR=E(_QM);if(!_QR._){var _QS=_QR.a,_QT=_QR.b,_QU=_QR.c,_QV=_QR.d;if((imul(3,_QS)|0)>=_QN){if((imul(3,_QN)|0)>=_QS){return new T4(0,(_QS+_QN|0)+1|0,E(_QL),E(_QR),E(new T4(0,_QN,E(_QO),E(_QP),E(_QQ))));}else{return new F(function(){return _Js(_QT,_QU,B(_QK(_QL,_QV,_QN,_QO,_QP,_QQ)));});}}else{return new F(function(){return _IQ(_QO,B(_QW(_QL,_QS,_QT,_QU,_QV,_QP)),_QQ);});}}else{return new F(function(){return _QE(_QL,_QN,_QO,_QP,_QQ);});}},_QW=function(_QX,_QY,_QZ,_R0,_R1,_R2){var _R3=E(_R2);if(!_R3._){var _R4=_R3.a,_R5=_R3.b,_R6=_R3.c,_R7=_R3.d;if((imul(3,_QY)|0)>=_R4){if((imul(3,_R4)|0)>=_QY){return new T4(0,(_QY+_R4|0)+1|0,E(_QX),E(new T4(0,_QY,E(_QZ),E(_R0),E(_R1))),E(_R3));}else{return new F(function(){return _Js(_QZ,_R0,B(_QK(_QX,_R1,_R4,_R5,_R6,_R7)));});}}else{return new F(function(){return _IQ(_R5,B(_QW(_QX,_QY,_QZ,_R0,_R1,_R6)),_R7);});}}else{return new F(function(){return _Qy(_QX,_QY,_QZ,_R0,_R1);});}},_R8=function(_R9,_Ra,_Rb){var _Rc=E(_Ra);if(!_Rc._){var _Rd=_Rc.a,_Re=_Rc.b,_Rf=_Rc.c,_Rg=_Rc.d,_Rh=E(_Rb);if(!_Rh._){var _Ri=_Rh.a,_Rj=_Rh.b,_Rk=_Rh.c,_Rl=_Rh.d;if((imul(3,_Rd)|0)>=_Ri){if((imul(3,_Ri)|0)>=_Rd){return new T4(0,(_Rd+_Ri|0)+1|0,E(_R9),E(_Rc),E(_Rh));}else{return new F(function(){return _Js(_Re,_Rf,B(_QK(_R9,_Rg,_Ri,_Rj,_Rk,_Rl)));});}}else{return new F(function(){return _IQ(_Rj,B(_QW(_R9,_Rd,_Re,_Rf,_Rg,_Rk)),_Rl);});}}else{return new F(function(){return _Qy(_R9,_Rd,_Re,_Rf,_Rg);});}}else{return new F(function(){return _Qq(_R9,_Rb);});}},_Rm=function(_Rn,_Ro,_Rp,_Rq){var _Rr=E(_Rq);if(!_Rr._){var _Rs=new T(function(){var _Rt=B(_Rm(_Rr.a,_Rr.b,_Rr.c,_Rr.d));return new T2(0,_Rt.a,_Rt.b);});return new T2(0,new T(function(){return E(E(_Rs).a);}),new T(function(){return B(_IQ(_Ro,_Rp,E(_Rs).b));}));}else{return new T2(0,_Ro,_Rp);}},_Ru=function(_Rv,_Rw,_Rx,_Ry){var _Rz=E(_Rx);if(!_Rz._){var _RA=new T(function(){var _RB=B(_Ru(_Rz.a,_Rz.b,_Rz.c,_Rz.d));return new T2(0,_RB.a,_RB.b);});return new T2(0,new T(function(){return E(E(_RA).a);}),new T(function(){return B(_Js(_Rw,E(_RA).b,_Ry));}));}else{return new T2(0,_Rw,_Ry);}},_RC=function(_RD,_RE){var _RF=E(_RD);if(!_RF._){var _RG=_RF.a,_RH=E(_RE);if(!_RH._){var _RI=_RH.a;if(_RG<=_RI){var _RJ=B(_Ru(_RI,_RH.b,_RH.c,_RH.d));return new F(function(){return _IQ(_RJ.a,_RF,_RJ.b);});}else{var _RK=B(_Rm(_RG,_RF.b,_RF.c,_RF.d));return new F(function(){return _Js(_RK.a,_RK.b,_RH);});}}else{return E(_RF);}}else{return E(_RE);}},_RL=function(_RM,_RN,_RO,_RP,_RQ){var _RR=E(_RM);if(!_RR._){var _RS=_RR.a,_RT=_RR.b,_RU=_RR.c,_RV=_RR.d;if((imul(3,_RS)|0)>=_RN){if((imul(3,_RN)|0)>=_RS){return new F(function(){return _RC(_RR,new T4(0,_RN,E(_RO),E(_RP),E(_RQ)));});}else{return new F(function(){return _Js(_RT,_RU,B(_RL(_RV,_RN,_RO,_RP,_RQ)));});}}else{return new F(function(){return _IQ(_RO,B(_RW(_RS,_RT,_RU,_RV,_RP)),_RQ);});}}else{return new T4(0,_RN,E(_RO),E(_RP),E(_RQ));}},_RW=function(_RX,_RY,_RZ,_S0,_S1){var _S2=E(_S1);if(!_S2._){var _S3=_S2.a,_S4=_S2.b,_S5=_S2.c,_S6=_S2.d;if((imul(3,_RX)|0)>=_S3){if((imul(3,_S3)|0)>=_RX){return new F(function(){return _RC(new T4(0,_RX,E(_RY),E(_RZ),E(_S0)),_S2);});}else{return new F(function(){return _Js(_RY,_RZ,B(_RL(_S0,_S3,_S4,_S5,_S6)));});}}else{return new F(function(){return _IQ(_S4,B(_RW(_RX,_RY,_RZ,_S0,_S5)),_S6);});}}else{return new T4(0,_RX,E(_RY),E(_RZ),E(_S0));}},_S7=function(_S8,_S9){var _Sa=E(_S8);if(!_Sa._){var _Sb=_Sa.a,_Sc=_Sa.b,_Sd=_Sa.c,_Se=_Sa.d,_Sf=E(_S9);if(!_Sf._){var _Sg=_Sf.a,_Sh=_Sf.b,_Si=_Sf.c,_Sj=_Sf.d;if((imul(3,_Sb)|0)>=_Sg){if((imul(3,_Sg)|0)>=_Sb){return new F(function(){return _RC(_Sa,_Sf);});}else{return new F(function(){return _Js(_Sc,_Sd,B(_RL(_Se,_Sg,_Sh,_Si,_Sj)));});}}else{return new F(function(){return _IQ(_Sh,B(_RW(_Sb,_Sc,_Sd,_Se,_Si)),_Sj);});}}else{return E(_Sa);}}else{return E(_S9);}},_Sk=function(_Sl,_Sm){var _Sn=E(_Sm);if(!_Sn._){var _So=_Sn.b,_Sp=_Sn.c,_Sq=_Sn.d;if(!B(A1(_Sl,_So))){return new F(function(){return _S7(B(_Sk(_Sl,_Sp)),B(_Sk(_Sl,_Sq)));});}else{return new F(function(){return _R8(_So,B(_Sk(_Sl,_Sp)),B(_Sk(_Sl,_Sq)));});}}else{return new T0(1);}},_Sr=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_Ss=new T(function(){return B(err(_Sr));}),_St=function(_Su,_Sv,_Sw,_Sx){while(1){var _Sy=E(_Sw);if(!_Sy._){_Su=_Sy.a;_Sv=_Sy.b;_Sw=_Sy.c;_Sx=_Sy.d;continue;}else{return E(_Sv);}}},_Sz=function(_SA,_SB,_SC){return new T3(0,E(_SA),E(_SB),E(_SC));},_SD=function(_SE,_SF){var _SG=E(_SE);if(!_SG._){return __Z;}else{var _SH=E(_SF);return (_SH._==0)?__Z:new T2(1,new T(function(){var _SI=E(_SH.a);return B(_Sz(_SG.a,_SI.a,_SI.b));}),new T(function(){return B(_SD(_SG.b,_SH.b));}));}},_SJ=function(_SK,_SL,_SM,_SN){var _SO=E(_SN);if(!_SO._){var _SP=_SO.c,_SQ=_SO.d,_SR=E(_SO.b),_SS=E(_SK),_ST=E(_SR.a);if(_SS>=_ST){if(_SS!=_ST){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SL,_SM,_SQ)));});}else{var _SU=E(_SL),_SV=E(_SR.b),_SW=E(_SU.a),_SX=E(_SV.a);if(_SW>=_SX){if(_SW!=_SX){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_SM,_SQ)));});}else{var _SY=E(_SU.b),_SZ=E(_SV.b);if(_SY>=_SZ){if(_SY!=_SZ){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_SM,_SQ)));});}else{var _T0=E(_SU.c),_T1=E(_SV.c);if(_T0>=_T1){if(_T0!=_T1){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_SM,_SQ)));});}else{var _T2=E(_SM),_T3=_T2.d,_T4=E(_T2.a),_T5=_T4.a,_T6=_T4.b,_T7=_T4.c,_T8=E(_T2.b),_T9=_T8.a,_Ta=_T8.b,_Tb=_T8.c,_Tc=E(_T2.c),_Td=_Tc.a,_Te=_Tc.b,_Tf=_Tc.c,_Tg=E(_T2.e),_Th=E(_SR.c),_Ti=_Th.d,_Tj=E(_Th.a),_Tk=_Tj.a,_Tl=_Tj.b,_Tm=_Tj.c,_Tn=E(_Th.b),_To=_Tn.a,_Tp=_Tn.b,_Tq=_Tn.c,_Tr=E(_Th.c),_Ts=_Tr.a,_Tt=_Tr.b,_Tu=_Tr.c,_Tv=E(_Th.e);if(_T5>=_Tk){if(_T5!=_Tk){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T6>=_Tl){if(_T6!=_Tl){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T7>=_Tm){if(_T7!=_Tm){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T9>=_To){if(_T9!=_To){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Ta>=_Tp){if(_Ta!=_Tp){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Tb>=_Tq){if(_Tb!=_Tq){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Td>=_Ts){if(_Td!=_Ts){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Te>=_Tt){if(_Te!=_Tt){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_Tf>=_Tu){if(_Tf!=_Tu){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{if(_T3>=_Ti){if(_T3!=_Ti){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{var _Tw=E(_Tg.a),_Tx=E(_Tv.a);if(_Tw>=_Tx){if(_Tw!=_Tx){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{var _Ty=E(_Tg.b),_Tz=E(_Tv.b);if(_Ty>=_Tz){if(_Ty!=_Tz){return new F(function(){return _IQ(_SR,_SP,B(_SJ(_SS,_SU,_T2,_SQ)));});}else{return new F(function(){return _RC(_SP,_SQ);});}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_T2,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_SM,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_SM,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SU,_SM,_SP)),_SQ);});}}}else{return new F(function(){return _Js(_SR,B(_SJ(_SS,_SL,_SM,_SP)),_SQ);});}}else{return new T0(1);}},_TA=function(_TB,_TC){while(1){var _TD=E(_TC);if(!_TD._){var _TE=E(_TD.b),_TF=B(_SJ(_TE.a,_TE.b,_TE.c,B(_TA(_TB,_TD.d))));_TB=_TF;_TC=_TD.c;continue;}else{return E(_TB);}}},_TG=function(_TH,_TI){while(1){var _TJ=E(_TI);if(!_TJ._){var _TK=E(_TJ.b),_TL=B(_SJ(_TK.a,_TK.b,_TK.c,B(_TG(_TH,_TJ.d))));_TH=_TL;_TI=_TJ.c;continue;}else{return E(_TH);}}},_TM=function(_TN,_TO,_TP){while(1){var _TQ=E(_TP);if(!_TQ._){return E(_TO);}else{_TN=_TQ.a;_TO=_TQ.b;_TP=_TQ.c;continue;}}},_TR=new T(function(){return B(unCStr("lookFor: Breakpoint does not exist."));}),_TS=new T(function(){return B(err(_TR));}),_TT=function(_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U1){var _U2=E(_U1);if(!_U2._){return __Z;}else{var _U3=E(_U2.b),_U4=E(_U3.a),_U5=_U4.b,_U6=_U4.c,_U7=E(_U3.b),_U8=_U7.b,_U9=_U7.c,_Ua=function(_Ub){var _Uc=_TW-_TZ,_Ud=function(_Ue){var _Uf=_U6-_U9,_Ug=function(_Uh){if(_Ue>=_Uh){if(_Ue<_Uh){return E(_TS);}else{return new F(function(){return _TT(_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U2.c);});}}else{return new F(function(){return _TT(_TU,_TV,_TW,_TX,_TY,_TZ,_U0,_U2.a);});}};if(_Uf!=0){if(_Uf<=0){if( -_Uf>=1.0e-7){var _Ui=E(_U0);return new F(function(){return _Ug((_U6*_U8+Math.sqrt(((_U5-_U8)*(_U5-_U8)+_Uf*_Uf)*(_U6-_Ui)*(_U9-_Ui))+(_U5*(_Ui-_U9)-_U8*_Ui))/_Uf);});}else{return new F(function(){return _Ug((_U5+_U8)/2);});}}else{if(_Uf>=1.0e-7){var _Uj=E(_U0);return new F(function(){return _Ug((_U6*_U8+Math.sqrt(((_U5-_U8)*(_U5-_U8)+_Uf*_Uf)*(_U6-_Uj)*(_U9-_Uj))+(_U5*(_Uj-_U9)-_U8*_Uj))/_Uf);});}else{return new F(function(){return _Ug((_U5+_U8)/2);});}}}else{return new F(function(){return _Ug((_U5+_U8)/2);});}};if(_Uc!=0){if(_Uc<=0){if( -_Uc>=1.0e-7){var _Uk=E(_U0);return new F(function(){return _Ud((_TW*_TY+Math.sqrt(((_TV-_TY)*(_TV-_TY)+_Uc*_Uc)*(_TW-_Uk)*(_TZ-_Uk))+(_TV*(_Uk-_TZ)-_TY*_Uk))/_Uc);});}else{return new F(function(){return _Ud((_TV+_TY)/2);});}}else{if(_Uc>=1.0e-7){var _Ul=E(_U0);return new F(function(){return _Ud((_TW*_TY+Math.sqrt(((_TV-_TY)*(_TV-_TY)+_Uc*_Uc)*(_TW-_Ul)*(_TZ-_Ul))+(_TV*(_Ul-_TZ)-_TY*_Ul))/_Uc);});}else{return new F(function(){return _Ud((_TV+_TY)/2);});}}}else{return new F(function(){return _Ud((_TV+_TY)/2);});}};if(_U4.a!=_TU){return new F(function(){return _Ua(_);});}else{if(_U7.a!=_TX){return new F(function(){return _Ua(_);});}else{return E(_U2);}}}},_Um=function(_Un,_Uo,_Up){var _Uq=E(_Up);if(!_Uq._){return __Z;}else{var _Ur=E(_Uq.b),_Us=E(_Ur.a),_Ut=_Us.b,_Uu=_Us.c,_Uv=E(_Ur.b),_Uw=_Uv.b,_Ux=_Uv.c,_Uy=E(_Un),_Uz=E(_Uy.a),_UA=_Uz.a,_UB=_Uz.b,_UC=_Uz.c,_UD=E(_Uy.b),_UE=_UD.a,_UF=_UD.b,_UG=_UD.c,_UH=function(_UI){var _UJ=_UC-_UG,_UK=function(_UL){var _UM=_Uu-_Ux,_UN=function(_UO){if(_UL>=_UO){if(_UL<_UO){return E(_TS);}else{return new F(function(){return _TT(_UA,_UB,_UC,_UE,_UF,_UG,_Uo,_Uq.c);});}}else{return new F(function(){return _TT(_UA,_UB,_UC,_UE,_UF,_UG,_Uo,_Uq.a);});}};if(_UM!=0){if(_UM<=0){if( -_UM>=1.0e-7){var _UP=E(_Uo);return new F(function(){return _UN((_Uu*_Uw+Math.sqrt(((_Ut-_Uw)*(_Ut-_Uw)+_UM*_UM)*(_Uu-_UP)*(_Ux-_UP))+(_Ut*(_UP-_Ux)-_Uw*_UP))/_UM);});}else{return new F(function(){return _UN((_Ut+_Uw)/2);});}}else{if(_UM>=1.0e-7){var _UQ=E(_Uo);return new F(function(){return _UN((_Uu*_Uw+Math.sqrt(((_Ut-_Uw)*(_Ut-_Uw)+_UM*_UM)*(_Uu-_UQ)*(_Ux-_UQ))+(_Ut*(_UQ-_Ux)-_Uw*_UQ))/_UM);});}else{return new F(function(){return _UN((_Ut+_Uw)/2);});}}}else{return new F(function(){return _UN((_Ut+_Uw)/2);});}};if(_UJ!=0){if(_UJ<=0){if( -_UJ>=1.0e-7){var _UR=E(_Uo);return new F(function(){return _UK((_UC*_UF+Math.sqrt(((_UB-_UF)*(_UB-_UF)+_UJ*_UJ)*(_UC-_UR)*(_UG-_UR))+(_UB*(_UR-_UG)-_UF*_UR))/_UJ);});}else{return new F(function(){return _UK((_UB+_UF)/2);});}}else{if(_UJ>=1.0e-7){var _US=E(_Uo);return new F(function(){return _UK((_UC*_UF+Math.sqrt(((_UB-_UF)*(_UB-_UF)+_UJ*_UJ)*(_UC-_US)*(_UG-_US))+(_UB*(_US-_UG)-_UF*_US))/_UJ);});}else{return new F(function(){return _UK((_UB+_UF)/2);});}}}else{return new F(function(){return _UK((_UB+_UF)/2);});}};if(_Us.a!=_UA){return new F(function(){return _UH(_);});}else{if(_Uv.a!=_UE){return new F(function(){return _UH(_);});}else{return E(_Uq);}}}},_UT=new T3(0,0,0,0),_UU=new T2(0,E(_UT),E(_UT)),_UV=function(_UW,_UX,_UY){var _UZ=function(_V0){var _V1=E(_UY);if(!_V1._){return E(_UU);}else{var _V2=E(_V1.b),_V3=E(_V2.a),_V4=_V3.b,_V5=_V3.c,_V6=E(_V2.b),_V7=_V6.b,_V8=_V6.c,_V9=E(_UW),_Va=E(_V9.a),_Vb=_Va.a,_Vc=E(_V9.b),_Vd=_Vc.a,_Ve=function(_Vf){var _Vg=B(_NC(_Va.b,_Va.c,_Vc.b,_Vc.c,_UX)),_Vh=_V5-_V8,_Vi=function(_Vj){if(_Vg>=_Vj){if(_Vg<=_Vj){return E(_UU);}else{var _Vk=function(_Vl,_Vm){var _Vn=E(_Vm);if(!_Vn._){return E(_Vl);}else{var _Vo=E(_Vn.b),_Vp=E(_Vo.a),_Vq=_Vp.b,_Vr=_Vp.c,_Vs=E(_Vo.b),_Vt=_Vs.b,_Vu=_Vs.c,_Vv=function(_Vw){var _Vx=_Vr-_Vu,_Vy=function(_Vz){if(_Vg>=_Vz){if(_Vg<=_Vz){return E(_Vl);}else{return new F(function(){return _Vk(_Vo,_Vn.c);});}}else{return new F(function(){return _Vk(_Vl,_Vn.a);});}};if(_Vx!=0){if(_Vx<=0){if( -_Vx>=1.0e-7){var _VA=E(_UX);return new F(function(){return _Vy((_Vr*_Vt+Math.sqrt(((_Vq-_Vt)*(_Vq-_Vt)+_Vx*_Vx)*(_Vr-_VA)*(_Vu-_VA))+(_Vq*(_VA-_Vu)-_Vt*_VA))/_Vx);});}else{return new F(function(){return _Vy((_Vq+_Vt)/2);});}}else{if(_Vx>=1.0e-7){var _VB=E(_UX);return new F(function(){return _Vy((_Vr*_Vt+Math.sqrt(((_Vq-_Vt)*(_Vq-_Vt)+_Vx*_Vx)*(_Vr-_VB)*(_Vu-_VB))+(_Vq*(_VB-_Vu)-_Vt*_VB))/_Vx);});}else{return new F(function(){return _Vy((_Vq+_Vt)/2);});}}}else{return new F(function(){return _Vy((_Vq+_Vt)/2);});}};if(_Vp.a!=_Vb){return new F(function(){return _Vv(_);});}else{if(_Vs.a!=_Vd){return new F(function(){return _Vv(_);});}else{return E(_Vl);}}}};return new F(function(){return _Vk(_V2,_V1.c);});}}else{var _VC=function(_VD,_VE){var _VF=E(_VE);if(!_VF._){return E(_VD);}else{var _VG=E(_VF.b),_VH=E(_VG.a),_VI=_VH.b,_VJ=_VH.c,_VK=E(_VG.b),_VL=_VK.b,_VM=_VK.c,_VN=function(_VO){var _VP=_VJ-_VM,_VQ=function(_VR){if(_Vg>=_VR){if(_Vg<=_VR){return E(_VD);}else{return new F(function(){return _VC(_VG,_VF.c);});}}else{return new F(function(){return _VC(_VD,_VF.a);});}};if(_VP!=0){if(_VP<=0){if( -_VP>=1.0e-7){var _VS=E(_UX);return new F(function(){return _VQ((_VJ*_VL+Math.sqrt(((_VI-_VL)*(_VI-_VL)+_VP*_VP)*(_VJ-_VS)*(_VM-_VS))+(_VI*(_VS-_VM)-_VL*_VS))/_VP);});}else{return new F(function(){return _VQ((_VI+_VL)/2);});}}else{if(_VP>=1.0e-7){var _VT=E(_UX);return new F(function(){return _VQ((_VJ*_VL+Math.sqrt(((_VI-_VL)*(_VI-_VL)+_VP*_VP)*(_VJ-_VT)*(_VM-_VT))+(_VI*(_VT-_VM)-_VL*_VT))/_VP);});}else{return new F(function(){return _VQ((_VI+_VL)/2);});}}}else{return new F(function(){return _VQ((_VI+_VL)/2);});}};if(_VH.a!=_Vb){return new F(function(){return _VN(_);});}else{if(_VK.a!=_Vd){return new F(function(){return _VN(_);});}else{return E(_VD);}}}};return new F(function(){return _VC(_UU,_V1.a);});}};if(_Vh!=0){if(_Vh<=0){if( -_Vh>=1.0e-7){var _VU=E(_UX);return new F(function(){return _Vi((_V5*_V7+Math.sqrt(((_V4-_V7)*(_V4-_V7)+_Vh*_Vh)*(_V5-_VU)*(_V8-_VU))+(_V4*(_VU-_V8)-_V7*_VU))/_Vh);});}else{return new F(function(){return _Vi((_V4+_V7)/2);});}}else{if(_Vh>=1.0e-7){var _VV=E(_UX);return new F(function(){return _Vi((_V5*_V7+Math.sqrt(((_V4-_V7)*(_V4-_V7)+_Vh*_Vh)*(_V5-_VV)*(_V8-_VV))+(_V4*(_VV-_V8)-_V7*_VV))/_Vh);});}else{return new F(function(){return _Vi((_V4+_V7)/2);});}}}else{return new F(function(){return _Vi((_V4+_V7)/2);});}};if(_V3.a!=_Vb){return new F(function(){return _Ve(_);});}else{if(_V6.a!=_Vd){return new F(function(){return _Ve(_);});}else{return E(_UU);}}}},_VW=B(_Um(_UW,_UX,_UY));if(!_VW._){return new F(function(){return _UZ(_);});}else{var _VX=E(_VW.a);if(!_VX._){return new F(function(){return _UZ(_);});}else{return new F(function(){return _TM(_VX.a,_VX.b,_VX.c);});}}},_VY=function(_VZ,_W0,_W1){var _W2=function(_W3){var _W4=E(_W1);if(!_W4._){return E(_UU);}else{var _W5=E(_W4.b),_W6=E(_W5.a),_W7=_W6.b,_W8=_W6.c,_W9=E(_W5.b),_Wa=_W9.b,_Wb=_W9.c,_Wc=E(_VZ),_Wd=E(_Wc.a),_We=_Wd.a,_Wf=E(_Wc.b),_Wg=_Wf.a,_Wh=function(_Wi){var _Wj=B(_NC(_Wd.b,_Wd.c,_Wf.b,_Wf.c,_W0)),_Wk=_W8-_Wb,_Wl=function(_Wm){if(_Wj>=_Wm){if(_Wj<=_Wm){return E(_UU);}else{var _Wn=function(_Wo,_Wp){var _Wq=E(_Wp);if(!_Wq._){return E(_Wo);}else{var _Wr=E(_Wq.b),_Ws=E(_Wr.a),_Wt=_Ws.b,_Wu=_Ws.c,_Wv=E(_Wr.b),_Ww=_Wv.b,_Wx=_Wv.c,_Wy=function(_Wz){var _WA=_Wu-_Wx,_WB=function(_WC){if(_Wj>=_WC){if(_Wj<=_WC){return E(_Wo);}else{return new F(function(){return _Wn(_Wo,_Wq.c);});}}else{return new F(function(){return _Wn(_Wr,_Wq.a);});}};if(_WA!=0){if(_WA<=0){if( -_WA>=1.0e-7){var _WD=E(_W0);return new F(function(){return _WB((_Wu*_Ww+Math.sqrt(((_Wt-_Ww)*(_Wt-_Ww)+_WA*_WA)*(_Wu-_WD)*(_Wx-_WD))+(_Wt*(_WD-_Wx)-_Ww*_WD))/_WA);});}else{return new F(function(){return _WB((_Wt+_Ww)/2);});}}else{if(_WA>=1.0e-7){var _WE=E(_W0);return new F(function(){return _WB((_Wu*_Ww+Math.sqrt(((_Wt-_Ww)*(_Wt-_Ww)+_WA*_WA)*(_Wu-_WE)*(_Wx-_WE))+(_Wt*(_WE-_Wx)-_Ww*_WE))/_WA);});}else{return new F(function(){return _WB((_Wt+_Ww)/2);});}}}else{return new F(function(){return _WB((_Wt+_Ww)/2);});}};if(_Ws.a!=_We){return new F(function(){return _Wy(_);});}else{if(_Wv.a!=_Wg){return new F(function(){return _Wy(_);});}else{return E(_Wo);}}}};return new F(function(){return _Wn(_UU,_W4.c);});}}else{var _WF=function(_WG,_WH){var _WI=E(_WH);if(!_WI._){return E(_WG);}else{var _WJ=E(_WI.b),_WK=E(_WJ.a),_WL=_WK.b,_WM=_WK.c,_WN=E(_WJ.b),_WO=_WN.b,_WP=_WN.c,_WQ=function(_WR){var _WS=_WM-_WP,_WT=function(_WU){if(_Wj>=_WU){if(_Wj<=_WU){return E(_WG);}else{return new F(function(){return _WF(_WG,_WI.c);});}}else{return new F(function(){return _WF(_WJ,_WI.a);});}};if(_WS!=0){if(_WS<=0){if( -_WS>=1.0e-7){var _WV=E(_W0);return new F(function(){return _WT((_WM*_WO+Math.sqrt(((_WL-_WO)*(_WL-_WO)+_WS*_WS)*(_WM-_WV)*(_WP-_WV))+(_WL*(_WV-_WP)-_WO*_WV))/_WS);});}else{return new F(function(){return _WT((_WL+_WO)/2);});}}else{if(_WS>=1.0e-7){var _WW=E(_W0);return new F(function(){return _WT((_WM*_WO+Math.sqrt(((_WL-_WO)*(_WL-_WO)+_WS*_WS)*(_WM-_WW)*(_WP-_WW))+(_WL*(_WW-_WP)-_WO*_WW))/_WS);});}else{return new F(function(){return _WT((_WL+_WO)/2);});}}}else{return new F(function(){return _WT((_WL+_WO)/2);});}};if(_WK.a!=_We){return new F(function(){return _WQ(_);});}else{if(_WN.a!=_Wg){return new F(function(){return _WQ(_);});}else{return E(_WG);}}}};return new F(function(){return _WF(_W5,_W4.a);});}};if(_Wk!=0){if(_Wk<=0){if( -_Wk>=1.0e-7){var _WX=E(_W0);return new F(function(){return _Wl((_W8*_Wa+Math.sqrt(((_W7-_Wa)*(_W7-_Wa)+_Wk*_Wk)*(_W8-_WX)*(_Wb-_WX))+(_W7*(_WX-_Wb)-_Wa*_WX))/_Wk);});}else{return new F(function(){return _Wl((_W7+_Wa)/2);});}}else{if(_Wk>=1.0e-7){var _WY=E(_W0);return new F(function(){return _Wl((_W8*_Wa+Math.sqrt(((_W7-_Wa)*(_W7-_Wa)+_Wk*_Wk)*(_W8-_WY)*(_Wb-_WY))+(_W7*(_WY-_Wb)-_Wa*_WY))/_Wk);});}else{return new F(function(){return _Wl((_W7+_Wa)/2);});}}}else{return new F(function(){return _Wl((_W7+_Wa)/2);});}};if(_W6.a!=_We){return new F(function(){return _Wh(_);});}else{if(_W9.a!=_Wg){return new F(function(){return _Wh(_);});}else{return E(_UU);}}}},_WZ=B(_Um(_VZ,_W0,_W1));if(!_WZ._){return new F(function(){return _W2(_);});}else{var _X0=E(_WZ.c);if(!_X0._){return new F(function(){return _W2(_);});}else{return new F(function(){return _LG(_X0.a,_X0.b,_X0.c);});}}},_X1=function(_X2,_X3,_X4,_X5){var _X6=E(_X5);if(!_X6._){return new T3(1,_ON,_X3,_ON);}else{var _X7=_X6.a,_X8=_X6.c,_X9=E(_X6.b),_Xa=E(_X9.a),_Xb=_Xa.b,_Xc=_Xa.c,_Xd=E(_X9.b),_Xe=_Xd.b,_Xf=_Xd.c,_Xg=_Xc-_Xf,_Xh=function(_Xi){return (_X2>=_Xi)?new T3(1,_X7,_X9,new T(function(){return B(_X1(_X2,_X3,_X4,_X8));})):new T3(1,new T(function(){return B(_X1(_X2,_X3,_X4,_X7));}),_X9,_X8);};if(_Xg!=0){if(_Xg<=0){if( -_Xg>=1.0e-7){var _Xj=E(_X4);return new F(function(){return _Xh((_Xc*_Xe+Math.sqrt(((_Xb-_Xe)*(_Xb-_Xe)+_Xg*_Xg)*(_Xc-_Xj)*(_Xf-_Xj))+(_Xb*(_Xj-_Xf)-_Xe*_Xj))/_Xg);});}else{return new F(function(){return _Xh((_Xb+_Xe)/2);});}}else{if(_Xg>=1.0e-7){var _Xk=E(_X4);return new F(function(){return _Xh((_Xc*_Xe+Math.sqrt(((_Xb-_Xe)*(_Xb-_Xe)+_Xg*_Xg)*(_Xc-_Xk)*(_Xf-_Xk))+(_Xb*(_Xk-_Xf)-_Xe*_Xk))/_Xg);});}else{return new F(function(){return _Xh((_Xb+_Xe)/2);});}}}else{return new F(function(){return _Xh((_Xb+_Xe)/2);});}}},_Xl=function(_Xm,_Xn,_Xo,_Xp){var _Xq=E(_Xp);if(!_Xq._){return new T3(1,_ON,_Xn,_ON);}else{var _Xr=_Xq.a,_Xs=_Xq.c,_Xt=E(_Xm),_Xu=E(_Xq.b),_Xv=E(_Xu.a),_Xw=_Xv.b,_Xx=_Xv.c,_Xy=E(_Xu.b),_Xz=_Xy.b,_XA=_Xy.c,_XB=_Xx-_XA,_XC=function(_XD){return (_Xt>=_XD)?new T3(1,_Xr,_Xu,new T(function(){return B(_X1(_Xt,_Xn,_Xo,_Xs));})):new T3(1,new T(function(){return B(_X1(_Xt,_Xn,_Xo,_Xr));}),_Xu,_Xs);};if(_XB!=0){if(_XB<=0){if( -_XB>=1.0e-7){var _XE=E(_Xo);return new F(function(){return _XC((_Xx*_Xz+Math.sqrt(((_Xw-_Xz)*(_Xw-_Xz)+_XB*_XB)*(_Xx-_XE)*(_XA-_XE))+(_Xw*(_XE-_XA)-_Xz*_XE))/_XB);});}else{return new F(function(){return _XC((_Xw+_Xz)/2);});}}else{if(_XB>=1.0e-7){var _XF=E(_Xo);return new F(function(){return _XC((_Xx*_Xz+Math.sqrt(((_Xw-_Xz)*(_Xw-_Xz)+_XB*_XB)*(_Xx-_XF)*(_XA-_XF))+(_Xw*(_XF-_XA)-_Xz*_XF))/_XB);});}else{return new F(function(){return _XC((_Xw+_Xz)/2);});}}}else{return new F(function(){return _XC((_Xw+_Xz)/2);});}}},_XG=0,_XH=new T(function(){return B(unCStr("Non-exhaustive guards in"));}),_XI=function(_XJ){return new F(function(){return _7G(new T1(0,new T(function(){return B(_7T(_XJ,_XH));})),_7q);});},_XK=new T(function(){return B(_XI("Fortune/Fortune.hs:(311,19)-(314,56)|multi-way if"));}),_XL=function(_XM,_XN){var _XO=E(_XM);return new F(function(){return _K2(_Iy,new T3(0,_XO.d,new T3(0,E(_XO.a).a,E(_XO.b).a,E(_XO.c).a),_XO),_XN);});},_XP=new T(function(){return B(_84("Fortune/Fortune.hs:(117,1)-(118,32)|function setVert"));}),_XQ=function(_XR,_XS){var _XT=E(E(_XR).a),_XU=E(E(_XS).a);return (_XT>=_XU)?(_XT!=_XU)?2:1:0;},_XV=function(_XW){var _XX=E(_XW),_XY=E(_XX.b);return new T2(0,_XY,_XX);},_XZ=0,_Y0=new T3(0,_XZ,_XZ,_XZ),_Y1=function(_Y2,_Y3){if(_Y2<=_Y3){var _Y4=function(_Y5){return new T2(1,_Y5,new T(function(){if(_Y5!=_Y3){return B(_Y4(_Y5+1|0));}else{return __Z;}}));};return new F(function(){return _Y4(_Y2);});}else{return __Z;}},_Y6=new T(function(){return B(_Y1(0,2147483647));}),_Y7=function(_Y8,_Y9){var _Ya=E(_Y9);return (_Ya._==0)?__Z:new T2(1,new T(function(){return B(A1(_Y8,_Ya.a));}),new T(function(){return B(_Y7(_Y8,_Ya.b));}));},_Yb=new T(function(){return B(unCStr("tail"));}),_Yc=new T(function(){return B(_f4(_Yb));}),_Yd=function(_Ye){return E(E(_Ye).b);},_Yf=new T2(1,_6,_6),_Yg=function(_Yh,_Yi){var _Yj=function(_Yk,_Yl){var _Ym=E(_Yk);if(!_Ym._){return E(_Yl);}else{var _Yn=_Ym.a,_Yo=E(_Yl);if(!_Yo._){return E(_Ym);}else{var _Yp=_Yo.a;return (B(A2(_Yh,_Yn,_Yp))==2)?new T2(1,_Yp,new T(function(){return B(_Yj(_Ym,_Yo.b));})):new T2(1,_Yn,new T(function(){return B(_Yj(_Ym.b,_Yo));}));}}},_Yq=function(_Yr){var _Ys=E(_Yr);if(!_Ys._){return __Z;}else{var _Yt=E(_Ys.b);return (_Yt._==0)?E(_Ys):new T2(1,new T(function(){return B(_Yj(_Ys.a,_Yt.a));}),new T(function(){return B(_Yq(_Yt.b));}));}},_Yu=new T(function(){return B(_Yv(B(_Yq(_6))));}),_Yv=function(_Yw){while(1){var _Yx=E(_Yw);if(!_Yx._){return E(_Yu);}else{if(!E(_Yx.b)._){return E(_Yx.a);}else{_Yw=B(_Yq(_Yx));continue;}}}},_Yy=new T(function(){return B(_Yz(_6));}),_YA=function(_YB,_YC,_YD){while(1){var _YE=B((function(_YF,_YG,_YH){var _YI=E(_YH);if(!_YI._){return new T2(1,new T2(1,_YF,_YG),_Yy);}else{var _YJ=_YI.a;if(B(A2(_Yh,_YF,_YJ))==2){var _YK=new T2(1,_YF,_YG);_YB=_YJ;_YC=_YK;_YD=_YI.b;return __continue;}else{return new T2(1,new T2(1,_YF,_YG),new T(function(){return B(_Yz(_YI));}));}}})(_YB,_YC,_YD));if(_YE!=__continue){return _YE;}}},_YL=function(_YM,_YN,_YO){while(1){var _YP=B((function(_YQ,_YR,_YS){var _YT=E(_YS);if(!_YT._){return new T2(1,new T(function(){return B(A1(_YR,new T2(1,_YQ,_6)));}),_Yy);}else{var _YU=_YT.a,_YV=_YT.b;switch(B(A2(_Yh,_YQ,_YU))){case 0:_YM=_YU;_YN=function(_YW){return new F(function(){return A1(_YR,new T2(1,_YQ,_YW));});};_YO=_YV;return __continue;case 1:_YM=_YU;_YN=function(_YX){return new F(function(){return A1(_YR,new T2(1,_YQ,_YX));});};_YO=_YV;return __continue;default:return new T2(1,new T(function(){return B(A1(_YR,new T2(1,_YQ,_6)));}),new T(function(){return B(_Yz(_YT));}));}}})(_YM,_YN,_YO));if(_YP!=__continue){return _YP;}}},_Yz=function(_YY){var _YZ=E(_YY);if(!_YZ._){return E(_Yf);}else{var _Z0=_YZ.a,_Z1=E(_YZ.b);if(!_Z1._){return new T2(1,_YZ,_6);}else{var _Z2=_Z1.a,_Z3=_Z1.b;if(B(A2(_Yh,_Z0,_Z2))==2){return new F(function(){return _YA(_Z2,new T2(1,_Z0,_6),_Z3);});}else{return new F(function(){return _YL(_Z2,function(_Z4){return new T2(1,_Z0,_Z4);},_Z3);});}}}};return new F(function(){return _Yv(B(_Yz(_Yi)));});},_Z5=function(_Z6,_Z7,_Z8){var _Z9=function(_Za,_Zb){while(1){var _Zc=B((function(_Zd,_Ze){var _Zf=E(_Ze);if(!_Zf._){var _Zg=_Zf.e,_Zh=E(_Zf.b),_Zi=_Zh.a,_Zj=_Zh.b,_Zk=new T(function(){var _Zl=E(_Zf.c);switch(_Zl._){case 0:return B(_Z9(_Zd,_Zg));break;case 1:var _Zm=E(_Zl.a),_Zn=E(_Zm.a);if(_Zn<0){return B(_Z9(_Zd,_Zg));}else{var _Zo=E(_Z7);if(_Zn>_Zo){return B(_Z9(_Zd,_Zg));}else{var _Zp=E(_Zm.b);if(_Zp<0){return B(_Z9(_Zd,_Zg));}else{var _Zq=E(_Z8);if(_Zp>_Zq){return B(_Z9(_Zd,_Zg));}else{var _Zr=B(_oZ(_Z6,E(_Zi))),_Zs=E(_Zr.a),_Zt=E(_Zr.b),_Zu=B(_oZ(_Z6,E(_Zj))),_Zv=E(_Zu.a),_Zw=E(_Zu.b),_Zx=Math.pow(_Zn-_Zs,2)+Math.pow(_Zp-_Zt,2)-(Math.pow(_Zn-_Zv,2)+Math.pow(_Zp-_Zw,2)),_Zy=function(_Zz,_ZA){var _ZB=E(_ZA);if(_ZB._==2){return new T2(1,new T(function(){var _ZC=E(_Zz);return new T4(0,E(_ZC.a),E(_ZC.b),E(_ZB.a),E(_ZB.b));}),new T(function(){return B(_Z9(_Zd,_Zg));}));}else{return new F(function(){return _Z9(_Zd,_Zg);});}},_ZD=function(_ZE){if(_ZE>=1.0e-2){return new T2(0,_Zh,_Zl);}else{var _ZF=new T(function(){var _ZG=_Zv-_Zs,_ZH=(Math.pow(_Zv,2)-Math.pow(_Zs,2)+Math.pow(_Zw,2)-Math.pow(_Zt,2))/2,_ZI=_Zw-_Zt,_ZJ=function(_ZK,_ZL){var _ZM=B(_PX(2,B(_Yg(function(_ZN,_ZO){var _ZP=E(_ZN),_ZQ=E(_ZL),_ZR=E(_ZO),_ZS=Math.pow(_ZK-E(_ZP.a),2)+Math.pow(_ZQ-E(_ZP.b),2),_ZT=Math.pow(_ZK-E(_ZR.a),2)+Math.pow(_ZQ-E(_ZR.b),2);return (_ZS>=_ZT)?(_ZS!=_ZT)?2:1:0;},_Z6))));if(!B(_Qj(_AW,_Zr,_ZM))){return false;}else{return new F(function(){return _Qj(_AW,_Zu,_ZM);});}},_ZU=function(_ZV,_ZW){var _ZX=B(_PX(2,B(_Yg(function(_ZY,_ZZ){var _100=E(_ZY),_101=E(_ZV),_102=E(_ZZ),_103=Math.pow(_101-E(_100.a),2)+Math.pow(_ZW-E(_100.b),2),_104=Math.pow(_101-E(_102.a),2)+Math.pow(_ZW-E(_102.b),2);return (_103>=_104)?(_103!=_104)?2:1:0;},_Z6))));if(!B(_Qj(_AW,_Zr,_ZX))){return false;}else{return new F(function(){return _Qj(_AW,_Zu,_ZX);});}},_105=function(_106){if(_Zw!=_Zt){var _107=new T(function(){return (_ZH-_ZG*0)/_ZI;}),_108=new T(function(){var _109=new T(function(){return (_ZH-_ZG*_Zo)/_ZI;});if(!B(_ZJ(0,_109))){return __Z;}else{return new T2(1,new T2(0,_XG,_109),_6);}});return (!B(_ZJ(0,_107)))?E(_108):new T2(1,new T2(0,_XG,_107),_108);}else{if(_Zv!=_Zs){var _10a=new T(function(){return (_ZH-_ZI*0)/_ZG;}),_10b=new T(function(){var _10c=new T(function(){return (_ZH-_ZI*_Zq)/_ZG;});if(!B(_ZU(_10c,_Zq))){return __Z;}else{return new T2(1,new T2(0,_10c,_Zq),_6);}});return (!B(_ZU(_10a,0)))?E(_10b):new T2(1,new T2(0,_10a,_XG),_10b);}else{return E(_XK);}}},_10d=function(_10e,_10f){var _10g=E(_10e),_10h=E(_10f),_10i=Math.pow(_Zn-E(_10g.a),2)+Math.pow(_Zp-E(_10g.b),2),_10j=Math.pow(_Zn-E(_10h.a),2)+Math.pow(_Zp-E(_10h.b),2);return (_10i>=_10j)?(_10i!=_10j)?E(_10h):E(_10g):E(_10g);};if(_Zw!=_Zt){if(_Zv!=_Zs){var _10k=new T(function(){return (_ZH-_ZG*0)/_ZI;}),_10l=new T(function(){var _10m=new T(function(){return (_ZH-_ZG*_Zo)/_ZI;}),_10n=new T(function(){var _10o=new T(function(){return (_ZH-_ZI*0)/_ZG;}),_10p=new T(function(){var _10q=new T(function(){return (_ZH-_ZI*_Zq)/_ZG;});if(!B(_ZU(_10q,_Zq))){return __Z;}else{return new T2(1,new T2(0,_10q,_Zq),_6);}});if(!B(_ZU(_10o,0))){return E(_10p);}else{return new T2(1,new T2(0,_10o,_XG),_10p);}});if(!B(_ZJ(0,_10m))){return E(_10n);}else{return new T2(1,new T2(0,_XG,_10m),_10n);}});if(!B(_ZJ(0,_10k))){var _10r=B(_f8(_10d,_10l));}else{var _10r=B(_f8(_10d,new T2(1,new T2(0,_XG,_10k),_10l)));}var _10s=_10r;}else{var _10s=B(_f8(_10d,B(_105(_))));}var _10t=_10s;}else{var _10t=B(_f8(_10d,B(_105(_))));}return new T2(2,E(_Zm),E(_10t));});return new T2(0,_Zh,_ZF);}};if(_Zx!=0){if(_Zx<=0){var _10u=B(_ZD( -_Zx));return B(_Zy(_10u.a,_10u.b));}else{var _10v=B(_ZD(_Zx));return B(_Zy(_10v.a,_10v.b));}}else{var _10w=B(_ZD(0));return B(_Zy(_10w.a,_10w.b));}}}}}break;default:return new T2(1,new T(function(){return new T4(0,E(_Zi),E(_Zj),E(_Zl.a),E(_Zl.b));}),new T(function(){return B(_Z9(_Zd,_Zg));}));}},1);_Za=_Zk;_Zb=_Zf.d;return __continue;}else{return E(_Zd);}})(_Za,_Zb));if(_Zc!=__continue){return _Zc;}}},_10x=function(_10y,_10z,_10A){var _10B=new T(function(){var _10C=E(_10y),_10D=_10C.b,_10E=_10C.c,_10F=_10C.d,_10G=E(_10C.a),_10H=_10G.a,_10I=_10G.b,_10J=new T(function(){var _10K=new T(function(){var _10L=function(_10M){var _10N=new T(function(){var _10O=E(_10I);if(!_10O._){var _10P=E(_10O.c);if(!_10P._){return B(_St(_10P.a,_10P.b,_10P.c,_10P.d));}else{return E(_10O.b);}}else{return E(_Ss);}}),_10Q=function(_10R){var _10S=new T(function(){var _10T=E(_10F);return new T5(0,1,E(_10T),new T4(0,_cm,_10E,_10D,new T(function(){return E(E(_10N).b);})),E(_wq),E(_wq));}),_10U=new T(function(){var _10V=E(_10I);if(!_10V._){var _10W=E(_10V.c);if(!_10W._){var _10X=E(B(_St(_10W.a,_10W.b,_10W.c,_10W.d)).c),_10Y=E(_10X.a),_10Z=E(_10X.b),_110=E(_10X.c);return {_:0,a:_10Y,b:_10Y.a,c:_10Z,d:_10Z.a,e:_110,f:_110.a,g:_10X.d,h:_10X.e};}else{var _111=E(E(_10V.b).c),_112=E(_111.a),_113=E(_111.b),_114=E(_111.c);return {_:0,a:_112,b:_112.a,c:_113,d:_113.a,e:_114,f:_114.a,g:_111.d,h:_111.e};}}else{return E(_Ss);}}),_115=new T(function(){return E(E(_10U).h);}),_116=new T(function(){return E(E(_10U).a);}),_117=new T(function(){return E(E(_10U).c);}),_118=new T(function(){return new T2(0,E(_116),E(_117));}),_119=new T(function(){return E(E(_10U).g);}),_11a=new T(function(){return (E(_119)+E(_10F))/2;}),_11b=new T(function(){return E(E(_10U).e);}),_11c=new T(function(){return new T2(0,E(_117),E(_11b));}),_11d=new T(function(){var _11e=E(_116).a,_11f=E(_11b).a,_11g=E(_117).a,_11h=function(_11i,_11j){var _11k=function(_11l,_11m){var _11n=new T(function(){return new T1(1,E(_115));}),_11o=function(_11p,_11q){return new T1(1,new T(function(){var _11r=E(_11q);switch(_11r._){case 0:return E(_11n);break;case 1:return new T2(2,E(_11r.a),E(_115));break;default:return E(_XP);}}));},_11s=function(_11t,_11u){return new T1(1,new T(function(){var _11v=E(_11u);switch(_11v._){case 0:return E(_11n);break;case 1:return new T2(2,E(_11v.a),E(_115));break;default:return E(_XP);}}));},_11w=B(_L5(_11s,_11i,_11j,B(_L5(_11o,_11l,_11m,_10E))));if(_11e>=_11f){return new F(function(){return _Iz(_11f,_11e,_11n,_11w);});}else{return new F(function(){return _Iz(_11e,_11f,_11n,_11w);});}};if(_11g>=_11f){return new F(function(){return _11k(_11f,_11g);});}else{return new F(function(){return _11k(_11g,_11f);});}};if(_11e>=_11g){return B(_11h(_11g,_11e));}else{return B(_11h(_11e,_11g));}}),_11x=new T(function(){var _11y=E(_118),_11z=E(_11y.a),_11A=E(_11y.b),_11B=E(_11c),_11C=E(_11B.a),_11D=E(_11B.b);return B(_Xl(new T(function(){return E(E(_115).a);},1),new T2(0,E(_11z),E(_11D)),_119,B(_NN(_11z.a,_11z.b,_11z.c,_11A.a,_11A.b,_11A.c,_11C.a,_11C.b,_11C.c,_11D.a,_11D.b,_11D.c,_11a,_10D))));}),_11E=new T(function(){var _11F=B(_UV(_118,_11a,_10D)),_11G=E(_11F.a),_11H=_11G.a,_11I=_11G.b,_11J=_11G.c,_11K=E(_11F.b).a,_11L=B(_VY(_11c,_11a,_10D)),_11M=E(_11L.a).a,_11N=E(_11L.b),_11O=_11N.a,_11P=_11N.b,_11Q=_11N.c,_11R=new T(function(){var _11S=new T(function(){return E(E(_10U).f);}),_11T=new T(function(){return E(E(_10U).d);}),_11U=new T(function(){return E(E(_10U).b);}),_11V=function(_11W){return (E(_11M)==0)?(E(_11O)==0)?new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11H,_11U,_11T),_6)):new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11H,_11U,_11T),new T2(1,new T3(0,_11T,_11S,_11O),_6))):new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11H,_11U,_11T),new T2(1,new T3(0,_11T,_11S,_11O),_6)));};if(!E(_11H)){if(!E(_11K)){return new T2(1,new T3(0,_11U,_11T,_11S),new T2(1,new T3(0,_11T,_11S,_11O),_6));}else{return B(_11V(_));}}else{return B(_11V(_));}}),_11X=function(_11Y){return new F(function(){return _Qj(_wm,new T(function(){return E(E(_11Y).b);}),_11R);});},_11Z=B(_TG(_10I,B(_Sk(_11X,_10I)))),_120=function(_121){var _122=function(_123){var _124=function(_125){var _126=E(_125);if(!_126._){return E(_11Z);}else{var _127=E(_126.a);return new F(function(){return _K2(_Iy,new T3(0,_127.d,new T3(0,E(_127.a).a,E(_127.b).a,E(_127.c).a),_127),B(_124(_126.b)));});}};return new F(function(){return _124(B(_Q4(new T2(1,new T(function(){var _128=E(_116),_129=E(_11b);return B(_Lk(_Z8,_128.a,_128.b,_128.c,_129.a,_129.b,_129.c,_11O,_11P,_11Q));}),new T2(1,new T(function(){var _12a=E(_116),_12b=E(_11b);return B(_Lk(_Z8,_11H,_11I,_11J,_12a.a,_12a.b,_12a.c,_12b.a,_12b.b,_12b.c));}),_6)))));});};if(!E(_11M)){if(!E(_11O)){var _12c=E(_116),_12d=E(_11b),_12e=B(_Lk(_Z8,_11H,_11I,_11J,_12c.a,_12c.b,_12c.c,_12d.a,_12d.b,_12d.c));if(!_12e._){return E(_11Z);}else{return new F(function(){return _XL(_12e.a,_11Z);});}}else{return new F(function(){return _122(_);});}}else{return new F(function(){return _122(_);});}};if(!E(_11H)){if(!E(_11K)){var _12f=E(_116),_12g=E(_11b),_12h=B(_Lk(_Z8,_12f.a,_12f.b,_12f.c,_12g.a,_12g.b,_12g.c,_11O,_11P,_11Q));if(!_12h._){return E(_11Z);}else{return B(_XL(_12h.a,_11Z));}}else{return B(_120(_));}}else{return B(_120(_));}});return new T2(0,new T4(0,new T2(0,_10H,_11E),_11x,_11d,_119),_10S);},_12i=E(_10H);if(!_12i._){return new F(function(){return _10Q(_);});}else{var _12j=_12i.a,_12k=function(_12l){var _12m=new T(function(){var _12n=E(_12j);return new T3(0,_12n,_12n.a,_12n.c);}),_12o=new T(function(){return E(E(_12m).c);}),_12p=new T(function(){return E(E(_12m).a);}),_12q=new T(function(){var _12r=E(_12p),_12s=B(_OQ(_12r.a,_12r.b,_12r.c,_12o,_10D));return new T2(0,_12s.a,_12s.b);}),_12t=new T(function(){return E(E(_12q).b);}),_12u=new T(function(){var _12v=E(_12t);if(!_12v._){return E(E(_12v.a).a);}else{return E(E(_12v.a).b);}}),_12w=new T(function(){var _12x=function(_12y,_12z){var _12A=E(_12y),_12B=E(_12A.a);if(!E(_12B.a)){if(!E(E(_12A.b).a)){var _12C=__Z;}else{var _12C=new T1(1,new T3(0,0,_12B.b,_12B.c));}var _12D=_12C;}else{var _12D=new T1(1,_12B);}var _12E=new T(function(){var _12F=E(_12z),_12G=E(_12F.b);if(!E(E(_12F.a).a)){if(!E(_12G.a)){return __Z;}else{return new T1(1,_12G);}}else{return new T1(1,_12G);}}),_12H=E(_12D);if(!_12H._){var _12I=E(_10I);}else{var _12J=E(_12E);if(!_12J._){var _12K=E(_10I);}else{var _12L=new T(function(){return E(_12J.a).a;}),_12K=B(_TA(_10I,B(_Sk(function(_12M){var _12N=E(E(_12M).b);if(E(_12N.a)!=E(_12H.a).a){return false;}else{if(E(_12N.b)!=E(_12u).a){return false;}else{return new F(function(){return _w7(_12N.c,_12L);});}}},_10I))));}var _12I=_12K;}var _12O=function(_12P){var _12Q=E(_12P);if(!_12Q._){return E(_12I);}else{var _12R=E(_12Q.a);return new F(function(){return _K2(_Iy,new T3(0,_12R.d,new T3(0,E(_12R.a).a,E(_12R.b).a,E(_12R.c).a),_12R),B(_12O(_12Q.b)));});}};return new F(function(){return _12O(B(_Q4(new T2(1,new T(function(){var _12S=E(_12D);if(!_12S._){return __Z;}else{return B(_Qb(_Z8,_12S.a,_12u,_12p));}}),new T2(1,new T(function(){var _12T=E(_12E);if(!_12T._){return __Z;}else{return B(_Qb(_Z8,_12p,_12u,_12T.a));}}),_6)))));});},_12U=E(_12t);if(!_12U._){var _12V=_12U.a;return B(_12x(new T(function(){return B(_UV(_12V,_12o,_10D));}),_12V));}else{var _12W=_12U.a;return B(_12x(_12W,new T(function(){return B(_VY(_12W,_12o,_10D));})));}});return new T2(0,new T4(0,new T2(0,_12i.b,_12w),new T(function(){return E(E(_12q).a);}),new T(function(){var _12X=E(E(_12m).b),_12Y=E(_12u).a;if(_12X>=_12Y){return B(_Iz(_12Y,_12X,_Q3,_10E));}else{return B(_Iz(_12X,_12Y,_Q3,_10E));}}),_12o),new T(function(){var _12Z=E(_10F);return new T5(0,1,E(_12Z),new T4(0,_5i,_10E,_10D,_Y0),E(_wq),E(_wq));}));};if(!E(_10I)._){if(E(E(_10N).a)>E(_12j).c){return new F(function(){return _12k(_);});}else{return new F(function(){return _10Q(_);});}}else{return new F(function(){return _12k(_);});}}};if(!E(_10H)._){if(!E(_10I)._){var _130=B(_10L(_));return new T2(0,_130.a,_130.b);}else{return new T2(0,_10C,_wq);}}else{var _131=B(_10L(_));return new T2(0,_131.a,_131.b);}}),_132=B(_10x(new T(function(){return E(E(_10K).a);}),new T(function(){return B(_Ax(_10z,E(_10K).b));}),_));return new T2(0,_132.a,_132.b);});if(!E(_10H)._){if(!E(_10I)._){return E(_10J);}else{return new T2(0,new T(function(){return B(_Z9(_6,_10E));}),_wq);}}else{return E(_10J);}});return new T2(0,new T(function(){return E(E(_10B).a);}),new T(function(){return B(_Ax(_10z,E(_10B).b));}));},_133=new T(function(){return B(_SD(_Y6,new T(function(){return B(_Y7(_Yd,B(_Yg(_XQ,B(_Y7(_XV,_Z6))))));},1)));}),_134=new T(function(){var _135=B(_oZ(_133,0));return new T2(0,_135,_135.a);}),_136=new T(function(){var _137=B(_oZ(_133,1));return new T3(0,_137,_137.a,_137.c);}),_138=new T(function(){return E(E(_134).a);}),_139=new T(function(){return E(E(_136).a);}),_13a=new T3(1,_ON,new T(function(){return new T2(0,E(_138),E(_139));}),new T3(1,_ON,new T(function(){return new T2(0,E(_139),E(_138));}),_ON)),_13b=new T(function(){var _13c=E(E(_134).b),_13d=E(E(_136).b);if(_13c>=_13d){return new T5(0,1,E(new T2(0,_13d,_13c)),_Q3,E(_wq),E(_wq));}else{return new T5(0,1,E(new T2(0,_13c,_13d)),_Q3,E(_wq),E(_wq));}}),_13e=new T(function(){var _13f=E(_133);if(!_13f._){return E(_Yc);}else{var _13g=E(_13f.b);if(!_13g._){return E(_Yc);}else{var _13h=E(_13g.b);if(!_13h._){return new T2(0,new T(function(){return B(_Z9(_6,_13b));}),_wq);}else{var _13i=new T(function(){var _13j=E(_13h.a);return new T3(0,_13j,_13j.a,_13j.c);}),_13k=new T(function(){return E(E(_13i).c);}),_13l=new T(function(){return E(E(_13i).a);}),_13m=new T(function(){var _13n=E(_13l),_13o=B(_OQ(_13n.a,_13n.b,_13n.c,_13k,_13a));return new T2(0,_13o.a,_13o.b);}),_13p=new T(function(){return E(E(_13m).b);}),_13q=new T(function(){var _13r=E(_13p);if(!_13r._){return E(E(_13r.a).a);}else{return E(E(_13r.a).b);}}),_13s=new T(function(){var _13t=function(_13u,_13v){var _13w=E(_13u),_13x=E(_13w.a);if(!E(_13x.a)){if(!E(E(_13w.b).a)){var _13y=__Z;}else{var _13y=new T1(1,new T3(0,0,_13x.b,_13x.c));}var _13z=_13y;}else{var _13z=new T1(1,_13x);}var _13A=new T(function(){var _13B=E(_13v),_13C=E(_13B.b);if(!E(E(_13B.a).a)){if(!E(_13C.a)){return __Z;}else{return new T1(1,_13C);}}else{return new T1(1,_13C);}}),_13D=E(_13z);if(!_13D._){var _13E=new T0(1);}else{var _13F=E(_13A);if(!_13F._){var _13G=new T0(1);}else{var _13H=new T(function(){return E(_13F.a).a;}),_13G=B(_TA(_IL,B(_Sk(function(_13I){var _13J=E(E(_13I).b);if(E(_13J.a)!=E(_13D.a).a){return false;}else{if(E(_13J.b)!=E(_13q).a){return false;}else{return new F(function(){return _w7(_13J.c,_13H);});}}},_IL))));}var _13E=_13G;}var _13K=function(_13L){var _13M=E(_13L);if(!_13M._){return E(_13E);}else{var _13N=E(_13M.a);return new F(function(){return _K2(_Iy,new T3(0,_13N.d,new T3(0,E(_13N.a).a,E(_13N.b).a,E(_13N.c).a),_13N),B(_13K(_13M.b)));});}};return new F(function(){return _13K(B(_Q4(new T2(1,new T(function(){var _13O=E(_13z);if(!_13O._){return __Z;}else{return B(_Qb(_Z8,_13O.a,_13q,_13l));}}),new T2(1,new T(function(){var _13P=E(_13A);if(!_13P._){return __Z;}else{return B(_Qb(_Z8,_13l,_13q,_13P.a));}}),_6)))));});},_13Q=E(_13p);if(!_13Q._){var _13R=_13Q.a;return B(_13t(new T(function(){return B(_UV(_13R,_13k,_13a));}),_13R));}else{var _13S=_13Q.a;return B(_13t(_13S,new T(function(){return B(_VY(_13S,_13k,_13a));})));}}),_13T=B(_10x(new T4(0,new T2(0,_13h.b,_13s),new T(function(){return E(E(_13m).a);}),new T(function(){var _13U=E(E(_13i).b),_13V=E(_13q).a;if(_13U>=_13V){return B(_Iz(_13V,_13U,_Q3,_13b));}else{return B(_Iz(_13U,_13V,_Q3,_13b));}}),_13k),new T(function(){var _13W=E(E(_136).c);return new T5(0,1,E(_13W),new T4(0,_5i,_13b,_13a,_Y0),E(_wq),E(_wq));}),_));return new T2(0,_13T.a,_13T.b);}}}});return new T2(0,new T(function(){return E(E(_13e).a);}),new T(function(){return B(_Ax(_wq,E(_13e).b));}));},_13X=function(_13Y,_13Z){return (!E(_13Y))?false:E(_13Z);},_140=1,_141=function(_142){return new T1(1,_142);},_143=1,_144=new T(function(){return eval("(function(){return Util.height;})");}),_145=new T(function(){return eval("(function(){return Util.width;})");}),_146=function(_){var _147=E(_4r),_148=__app1(E(_145),_147),_149=__app1(E(_144),_147);return new T2(0,_148,_149);},_14a=function(_){var _14b=B(_146(_));return new T(function(){return E(E(_14b).a)/2;});},_14c=new T1(1,_14a),_14d=new T1(0,_ah),_14e=function(_14f,_14g,_14h,_14i,_){var _14j=function(_,_14k){var _14l=function(_,_14m){var _14n=function(_,_14o){var _14p=E(_14i);switch(_14p._){case 0:return new T(function(){var _14q=function(_14r){var _14s=_14r*256,_14t=_14s&4294967295,_14u=function(_14v){var _14w=E(_14m)*256,_14x=_14w&4294967295,_14y=function(_14z){var _14A=function(_14B){var _14C=_14B*256,_14D=_14C&4294967295,_14E=function(_14F){var _14G=E(_14p.a);return (1>_14G)?(0>_14G)?new T4(1,_14v,_14z,_14F,0):new T4(1,_14v,_14z,_14F,_14G):new T4(1,_14v,_14z,_14F,1);};if(_14C>=_14D){if(255>_14D){if(0>_14D){return new F(function(){return _14E(0);});}else{return new F(function(){return _14E(_14D);});}}else{return new F(function(){return _14E(255);});}}else{var _14H=_14D-1|0;if(255>_14H){if(0>_14H){return new F(function(){return _14E(0);});}else{return new F(function(){return _14E(_14H);});}}else{return new F(function(){return _14E(255);});}}},_14I=E(_14o);if(!_14I._){return new F(function(){return _14A(0);});}else{return new F(function(){return _14A(E(_14I.a));});}};if(_14w>=_14x){if(255>_14x){if(0>_14x){return new F(function(){return _14y(0);});}else{return new F(function(){return _14y(_14x);});}}else{return new F(function(){return _14y(255);});}}else{var _14J=_14x-1|0;if(255>_14J){if(0>_14J){return new F(function(){return _14y(0);});}else{return new F(function(){return _14y(_14J);});}}else{return new F(function(){return _14y(255);});}}};if(_14s>=_14t){if(255>_14t){if(0>_14t){return new F(function(){return _14u(0);});}else{return new F(function(){return _14u(_14t);});}}else{return new F(function(){return _14u(255);});}}else{var _14K=_14t-1|0;if(255>_14K){if(0>_14K){return new F(function(){return _14u(0);});}else{return new F(function(){return _14u(_14K);});}}else{return new F(function(){return _14u(255);});}}},_14L=E(_14k);if(!_14L._){return B(_14q(0));}else{return B(_14q(E(_14L.a)));}});case 1:var _14M=B(A1(_14p.a,_)),_14N=_14M;return new T(function(){var _14O=function(_14P){var _14Q=_14P*256,_14R=_14Q&4294967295,_14S=function(_14T){var _14U=E(_14m)*256,_14V=_14U&4294967295,_14W=function(_14X){var _14Y=function(_14Z){var _150=_14Z*256,_151=_150&4294967295,_152=function(_153){var _154=E(_14N);return (1>_154)?(0>_154)?new T4(1,_14T,_14X,_153,0):new T4(1,_14T,_14X,_153,_154):new T4(1,_14T,_14X,_153,1);};if(_150>=_151){if(255>_151){if(0>_151){return new F(function(){return _152(0);});}else{return new F(function(){return _152(_151);});}}else{return new F(function(){return _152(255);});}}else{var _155=_151-1|0;if(255>_155){if(0>_155){return new F(function(){return _152(0);});}else{return new F(function(){return _152(_155);});}}else{return new F(function(){return _152(255);});}}},_156=E(_14o);if(!_156._){return new F(function(){return _14Y(0);});}else{return new F(function(){return _14Y(E(_156.a));});}};if(_14U>=_14V){if(255>_14V){if(0>_14V){return new F(function(){return _14W(0);});}else{return new F(function(){return _14W(_14V);});}}else{return new F(function(){return _14W(255);});}}else{var _157=_14V-1|0;if(255>_157){if(0>_157){return new F(function(){return _14W(0);});}else{return new F(function(){return _14W(_157);});}}else{return new F(function(){return _14W(255);});}}};if(_14Q>=_14R){if(255>_14R){if(0>_14R){return new F(function(){return _14S(0);});}else{return new F(function(){return _14S(_14R);});}}else{return new F(function(){return _14S(255);});}}else{var _158=_14R-1|0;if(255>_158){if(0>_158){return new F(function(){return _14S(0);});}else{return new F(function(){return _14S(_158);});}}else{return new F(function(){return _14S(255);});}}},_159=E(_14k);if(!_159._){return B(_14O(0));}else{return B(_14O(E(_159.a)));}});case 2:var _15a=rMV(E(E(_14p.a).c)),_15b=E(_15a);return (_15b._==0)?new T(function(){var _15c=function(_15d){var _15e=_15d*256,_15f=_15e&4294967295,_15g=function(_15h){var _15i=E(_14m)*256,_15j=_15i&4294967295,_15k=function(_15l){var _15m=function(_15n){var _15o=_15n*256,_15p=_15o&4294967295,_15q=function(_15r){var _15s=B(A1(_14p.b,new T(function(){return B(_qv(_15b.a));})));return (1>_15s)?(0>_15s)?new T4(1,_15h,_15l,_15r,0):new T4(1,_15h,_15l,_15r,_15s):new T4(1,_15h,_15l,_15r,1);};if(_15o>=_15p){if(255>_15p){if(0>_15p){return new F(function(){return _15q(0);});}else{return new F(function(){return _15q(_15p);});}}else{return new F(function(){return _15q(255);});}}else{var _15t=_15p-1|0;if(255>_15t){if(0>_15t){return new F(function(){return _15q(0);});}else{return new F(function(){return _15q(_15t);});}}else{return new F(function(){return _15q(255);});}}},_15u=E(_14o);if(!_15u._){return new F(function(){return _15m(0);});}else{return new F(function(){return _15m(E(_15u.a));});}};if(_15i>=_15j){if(255>_15j){if(0>_15j){return new F(function(){return _15k(0);});}else{return new F(function(){return _15k(_15j);});}}else{return new F(function(){return _15k(255);});}}else{var _15v=_15j-1|0;if(255>_15v){if(0>_15v){return new F(function(){return _15k(0);});}else{return new F(function(){return _15k(_15v);});}}else{return new F(function(){return _15k(255);});}}};if(_15e>=_15f){if(255>_15f){if(0>_15f){return new F(function(){return _15g(0);});}else{return new F(function(){return _15g(_15f);});}}else{return new F(function(){return _15g(255);});}}else{var _15w=_15f-1|0;if(255>_15w){if(0>_15w){return new F(function(){return _15g(0);});}else{return new F(function(){return _15g(_15w);});}}else{return new F(function(){return _15g(255);});}}},_15x=E(_14k);if(!_15x._){return B(_15c(0));}else{return B(_15c(E(_15x.a)));}}):new T(function(){var _15y=function(_15z){var _15A=_15z*256,_15B=_15A&4294967295,_15C=function(_15D){var _15E=E(_14m)*256,_15F=_15E&4294967295,_15G=function(_15H){var _15I=function(_15J){var _15K=_15J*256,_15L=_15K&4294967295;if(_15K>=_15L){return (255>_15L)?(0>_15L)?new T4(1,_15D,_15H,0,1):new T4(1,_15D,_15H,_15L,1):new T4(1,_15D,_15H,255,1);}else{var _15M=_15L-1|0;return (255>_15M)?(0>_15M)?new T4(1,_15D,_15H,0,1):new T4(1,_15D,_15H,_15M,1):new T4(1,_15D,_15H,255,1);}},_15N=E(_14o);if(!_15N._){return new F(function(){return _15I(0);});}else{return new F(function(){return _15I(E(_15N.a));});}};if(_15E>=_15F){if(255>_15F){if(0>_15F){return new F(function(){return _15G(0);});}else{return new F(function(){return _15G(_15F);});}}else{return new F(function(){return _15G(255);});}}else{var _15O=_15F-1|0;if(255>_15O){if(0>_15O){return new F(function(){return _15G(0);});}else{return new F(function(){return _15G(_15O);});}}else{return new F(function(){return _15G(255);});}}};if(_15A>=_15B){if(255>_15B){if(0>_15B){return new F(function(){return _15C(0);});}else{return new F(function(){return _15C(_15B);});}}else{return new F(function(){return _15C(255);});}}else{var _15P=_15B-1|0;if(255>_15P){if(0>_15P){return new F(function(){return _15C(0);});}else{return new F(function(){return _15C(_15P);});}}else{return new F(function(){return _15C(255);});}}},_15Q=E(_14k);if(!_15Q._){return B(_15y(0));}else{return B(_15y(E(_15Q.a)));}});default:var _15R=rMV(E(E(_14p.a).c)),_15S=E(_15R);if(!_15S._){var _15T=B(A2(_14p.b,E(_15S.a).a,_)),_15U=_15T;return new T(function(){var _15V=function(_15W){var _15X=_15W*256,_15Y=_15X&4294967295,_15Z=function(_160){var _161=E(_14m)*256,_162=_161&4294967295,_163=function(_164){var _165=function(_166){var _167=_166*256,_168=_167&4294967295,_169=function(_16a){var _16b=E(_15U);return (1>_16b)?(0>_16b)?new T4(1,_160,_164,_16a,0):new T4(1,_160,_164,_16a,_16b):new T4(1,_160,_164,_16a,1);};if(_167>=_168){if(255>_168){if(0>_168){return new F(function(){return _169(0);});}else{return new F(function(){return _169(_168);});}}else{return new F(function(){return _169(255);});}}else{var _16c=_168-1|0;if(255>_16c){if(0>_16c){return new F(function(){return _169(0);});}else{return new F(function(){return _169(_16c);});}}else{return new F(function(){return _169(255);});}}},_16d=E(_14o);if(!_16d._){return new F(function(){return _165(0);});}else{return new F(function(){return _165(E(_16d.a));});}};if(_161>=_162){if(255>_162){if(0>_162){return new F(function(){return _163(0);});}else{return new F(function(){return _163(_162);});}}else{return new F(function(){return _163(255);});}}else{var _16e=_162-1|0;if(255>_16e){if(0>_16e){return new F(function(){return _163(0);});}else{return new F(function(){return _163(_16e);});}}else{return new F(function(){return _163(255);});}}};if(_15X>=_15Y){if(255>_15Y){if(0>_15Y){return new F(function(){return _15Z(0);});}else{return new F(function(){return _15Z(_15Y);});}}else{return new F(function(){return _15Z(255);});}}else{var _16f=_15Y-1|0;if(255>_16f){if(0>_16f){return new F(function(){return _15Z(0);});}else{return new F(function(){return _15Z(_16f);});}}else{return new F(function(){return _15Z(255);});}}},_16g=E(_14k);if(!_16g._){return B(_15V(0));}else{return B(_15V(E(_16g.a)));}});}else{return new T(function(){var _16h=function(_16i){var _16j=_16i*256,_16k=_16j&4294967295,_16l=function(_16m){var _16n=E(_14m)*256,_16o=_16n&4294967295,_16p=function(_16q){var _16r=function(_16s){var _16t=_16s*256,_16u=_16t&4294967295;if(_16t>=_16u){return (255>_16u)?(0>_16u)?new T4(1,_16m,_16q,0,1):new T4(1,_16m,_16q,_16u,1):new T4(1,_16m,_16q,255,1);}else{var _16v=_16u-1|0;return (255>_16v)?(0>_16v)?new T4(1,_16m,_16q,0,1):new T4(1,_16m,_16q,_16v,1):new T4(1,_16m,_16q,255,1);}},_16w=E(_14o);if(!_16w._){return new F(function(){return _16r(0);});}else{return new F(function(){return _16r(E(_16w.a));});}};if(_16n>=_16o){if(255>_16o){if(0>_16o){return new F(function(){return _16p(0);});}else{return new F(function(){return _16p(_16o);});}}else{return new F(function(){return _16p(255);});}}else{var _16x=_16o-1|0;if(255>_16x){if(0>_16x){return new F(function(){return _16p(0);});}else{return new F(function(){return _16p(_16x);});}}else{return new F(function(){return _16p(255);});}}};if(_16j>=_16k){if(255>_16k){if(0>_16k){return new F(function(){return _16l(0);});}else{return new F(function(){return _16l(_16k);});}}else{return new F(function(){return _16l(255);});}}else{var _16y=_16k-1|0;if(255>_16y){if(0>_16y){return new F(function(){return _16l(0);});}else{return new F(function(){return _16l(_16y);});}}else{return new F(function(){return _16l(255);});}}},_16z=E(_14k);if(!_16z._){return B(_16h(0));}else{return B(_16h(E(_16z.a)));}});}}},_16A=E(_14h);switch(_16A._){case 0:return new F(function(){return _14n(_,new T1(1,_16A.a));});break;case 1:var _16B=B(A1(_16A.a,_));return new F(function(){return _14n(_,new T1(1,_16B));});break;case 2:var _16C=rMV(E(E(_16A.a).c)),_16D=E(_16C);if(!_16D._){var _16E=new T(function(){return B(A1(_16A.b,new T(function(){return B(_qv(_16D.a));})));});return new F(function(){return _14n(_,new T1(1,_16E));});}else{return new F(function(){return _14n(_,_2o);});}break;default:var _16F=rMV(E(E(_16A.a).c)),_16G=E(_16F);if(!_16G._){var _16H=B(A2(_16A.b,E(_16G.a).a,_));return new F(function(){return _14n(_,new T1(1,_16H));});}else{return new F(function(){return _14n(_,_2o);});}}},_16I=function(_){var _16J=function(_,_16K){var _16L=E(_14i);switch(_16L._){case 0:return new T(function(){var _16M=function(_16N){var _16O=_16N*256,_16P=_16O&4294967295,_16Q=function(_16R){var _16S=function(_16T){var _16U=_16T*256,_16V=_16U&4294967295,_16W=function(_16X){var _16Y=E(_16L.a);return (1>_16Y)?(0>_16Y)?new T4(1,_16R,0,_16X,0):new T4(1,_16R,0,_16X,_16Y):new T4(1,_16R,0,_16X,1);};if(_16U>=_16V){if(255>_16V){if(0>_16V){return new F(function(){return _16W(0);});}else{return new F(function(){return _16W(_16V);});}}else{return new F(function(){return _16W(255);});}}else{var _16Z=_16V-1|0;if(255>_16Z){if(0>_16Z){return new F(function(){return _16W(0);});}else{return new F(function(){return _16W(_16Z);});}}else{return new F(function(){return _16W(255);});}}},_170=E(_16K);if(!_170._){return new F(function(){return _16S(0);});}else{return new F(function(){return _16S(E(_170.a));});}};if(_16O>=_16P){if(255>_16P){if(0>_16P){return new F(function(){return _16Q(0);});}else{return new F(function(){return _16Q(_16P);});}}else{return new F(function(){return _16Q(255);});}}else{var _171=_16P-1|0;if(255>_171){if(0>_171){return new F(function(){return _16Q(0);});}else{return new F(function(){return _16Q(_171);});}}else{return new F(function(){return _16Q(255);});}}},_172=E(_14k);if(!_172._){return B(_16M(0));}else{return B(_16M(E(_172.a)));}});case 1:var _173=B(A1(_16L.a,_)),_174=_173;return new T(function(){var _175=function(_176){var _177=_176*256,_178=_177&4294967295,_179=function(_17a){var _17b=function(_17c){var _17d=_17c*256,_17e=_17d&4294967295,_17f=function(_17g){var _17h=E(_174);return (1>_17h)?(0>_17h)?new T4(1,_17a,0,_17g,0):new T4(1,_17a,0,_17g,_17h):new T4(1,_17a,0,_17g,1);};if(_17d>=_17e){if(255>_17e){if(0>_17e){return new F(function(){return _17f(0);});}else{return new F(function(){return _17f(_17e);});}}else{return new F(function(){return _17f(255);});}}else{var _17i=_17e-1|0;if(255>_17i){if(0>_17i){return new F(function(){return _17f(0);});}else{return new F(function(){return _17f(_17i);});}}else{return new F(function(){return _17f(255);});}}},_17j=E(_16K);if(!_17j._){return new F(function(){return _17b(0);});}else{return new F(function(){return _17b(E(_17j.a));});}};if(_177>=_178){if(255>_178){if(0>_178){return new F(function(){return _179(0);});}else{return new F(function(){return _179(_178);});}}else{return new F(function(){return _179(255);});}}else{var _17k=_178-1|0;if(255>_17k){if(0>_17k){return new F(function(){return _179(0);});}else{return new F(function(){return _179(_17k);});}}else{return new F(function(){return _179(255);});}}},_17l=E(_14k);if(!_17l._){return B(_175(0));}else{return B(_175(E(_17l.a)));}});case 2:var _17m=rMV(E(E(_16L.a).c)),_17n=E(_17m);return (_17n._==0)?new T(function(){var _17o=function(_17p){var _17q=_17p*256,_17r=_17q&4294967295,_17s=function(_17t){var _17u=function(_17v){var _17w=_17v*256,_17x=_17w&4294967295,_17y=function(_17z){var _17A=B(A1(_16L.b,new T(function(){return B(_qv(_17n.a));})));return (1>_17A)?(0>_17A)?new T4(1,_17t,0,_17z,0):new T4(1,_17t,0,_17z,_17A):new T4(1,_17t,0,_17z,1);};if(_17w>=_17x){if(255>_17x){if(0>_17x){return new F(function(){return _17y(0);});}else{return new F(function(){return _17y(_17x);});}}else{return new F(function(){return _17y(255);});}}else{var _17B=_17x-1|0;if(255>_17B){if(0>_17B){return new F(function(){return _17y(0);});}else{return new F(function(){return _17y(_17B);});}}else{return new F(function(){return _17y(255);});}}},_17C=E(_16K);if(!_17C._){return new F(function(){return _17u(0);});}else{return new F(function(){return _17u(E(_17C.a));});}};if(_17q>=_17r){if(255>_17r){if(0>_17r){return new F(function(){return _17s(0);});}else{return new F(function(){return _17s(_17r);});}}else{return new F(function(){return _17s(255);});}}else{var _17D=_17r-1|0;if(255>_17D){if(0>_17D){return new F(function(){return _17s(0);});}else{return new F(function(){return _17s(_17D);});}}else{return new F(function(){return _17s(255);});}}},_17E=E(_14k);if(!_17E._){return B(_17o(0));}else{return B(_17o(E(_17E.a)));}}):new T(function(){var _17F=function(_17G){var _17H=_17G*256,_17I=_17H&4294967295,_17J=function(_17K){var _17L=function(_17M){var _17N=_17M*256,_17O=_17N&4294967295;if(_17N>=_17O){return (255>_17O)?(0>_17O)?new T4(1,_17K,0,0,1):new T4(1,_17K,0,_17O,1):new T4(1,_17K,0,255,1);}else{var _17P=_17O-1|0;return (255>_17P)?(0>_17P)?new T4(1,_17K,0,0,1):new T4(1,_17K,0,_17P,1):new T4(1,_17K,0,255,1);}},_17Q=E(_16K);if(!_17Q._){return new F(function(){return _17L(0);});}else{return new F(function(){return _17L(E(_17Q.a));});}};if(_17H>=_17I){if(255>_17I){if(0>_17I){return new F(function(){return _17J(0);});}else{return new F(function(){return _17J(_17I);});}}else{return new F(function(){return _17J(255);});}}else{var _17R=_17I-1|0;if(255>_17R){if(0>_17R){return new F(function(){return _17J(0);});}else{return new F(function(){return _17J(_17R);});}}else{return new F(function(){return _17J(255);});}}},_17S=E(_14k);if(!_17S._){return B(_17F(0));}else{return B(_17F(E(_17S.a)));}});default:var _17T=rMV(E(E(_16L.a).c)),_17U=E(_17T);if(!_17U._){var _17V=B(A2(_16L.b,E(_17U.a).a,_)),_17W=_17V;return new T(function(){var _17X=function(_17Y){var _17Z=_17Y*256,_180=_17Z&4294967295,_181=function(_182){var _183=function(_184){var _185=_184*256,_186=_185&4294967295,_187=function(_188){var _189=E(_17W);return (1>_189)?(0>_189)?new T4(1,_182,0,_188,0):new T4(1,_182,0,_188,_189):new T4(1,_182,0,_188,1);};if(_185>=_186){if(255>_186){if(0>_186){return new F(function(){return _187(0);});}else{return new F(function(){return _187(_186);});}}else{return new F(function(){return _187(255);});}}else{var _18a=_186-1|0;if(255>_18a){if(0>_18a){return new F(function(){return _187(0);});}else{return new F(function(){return _187(_18a);});}}else{return new F(function(){return _187(255);});}}},_18b=E(_16K);if(!_18b._){return new F(function(){return _183(0);});}else{return new F(function(){return _183(E(_18b.a));});}};if(_17Z>=_180){if(255>_180){if(0>_180){return new F(function(){return _181(0);});}else{return new F(function(){return _181(_180);});}}else{return new F(function(){return _181(255);});}}else{var _18c=_180-1|0;if(255>_18c){if(0>_18c){return new F(function(){return _181(0);});}else{return new F(function(){return _181(_18c);});}}else{return new F(function(){return _181(255);});}}},_18d=E(_14k);if(!_18d._){return B(_17X(0));}else{return B(_17X(E(_18d.a)));}});}else{return new T(function(){var _18e=function(_18f){var _18g=_18f*256,_18h=_18g&4294967295,_18i=function(_18j){var _18k=function(_18l){var _18m=_18l*256,_18n=_18m&4294967295;if(_18m>=_18n){return (255>_18n)?(0>_18n)?new T4(1,_18j,0,0,1):new T4(1,_18j,0,_18n,1):new T4(1,_18j,0,255,1);}else{var _18o=_18n-1|0;return (255>_18o)?(0>_18o)?new T4(1,_18j,0,0,1):new T4(1,_18j,0,_18o,1):new T4(1,_18j,0,255,1);}},_18p=E(_16K);if(!_18p._){return new F(function(){return _18k(0);});}else{return new F(function(){return _18k(E(_18p.a));});}};if(_18g>=_18h){if(255>_18h){if(0>_18h){return new F(function(){return _18i(0);});}else{return new F(function(){return _18i(_18h);});}}else{return new F(function(){return _18i(255);});}}else{var _18q=_18h-1|0;if(255>_18q){if(0>_18q){return new F(function(){return _18i(0);});}else{return new F(function(){return _18i(_18q);});}}else{return new F(function(){return _18i(255);});}}},_18r=E(_14k);if(!_18r._){return B(_18e(0));}else{return B(_18e(E(_18r.a)));}});}}},_18s=E(_14h);switch(_18s._){case 0:return new F(function(){return _16J(_,new T1(1,_18s.a));});break;case 1:var _18t=B(A1(_18s.a,_));return new F(function(){return _16J(_,new T1(1,_18t));});break;case 2:var _18u=rMV(E(E(_18s.a).c)),_18v=E(_18u);if(!_18v._){var _18w=new T(function(){return B(A1(_18s.b,new T(function(){return B(_qv(_18v.a));})));});return new F(function(){return _16J(_,new T1(1,_18w));});}else{return new F(function(){return _16J(_,_2o);});}break;default:var _18x=rMV(E(E(_18s.a).c)),_18y=E(_18x);if(!_18y._){var _18z=B(A2(_18s.b,E(_18y.a).a,_));return new F(function(){return _16J(_,new T1(1,_18z));});}else{return new F(function(){return _16J(_,_2o);});}}},_18A=E(_14g);switch(_18A._){case 0:return new F(function(){return _14l(_,_18A.a);});break;case 1:var _18B=B(A1(_18A.a,_));return new F(function(){return _14l(_,_18B);});break;case 2:var _18C=rMV(E(E(_18A.a).c)),_18D=E(_18C);if(!_18D._){var _18E=new T(function(){return B(A1(_18A.b,new T(function(){return E(E(_18D.a).a);})));});return new F(function(){return _14l(_,_18E);});}else{return new F(function(){return _16I(_);});}break;default:var _18F=rMV(E(E(_18A.a).c)),_18G=E(_18F);if(!_18G._){var _18H=B(A2(_18A.b,E(_18G.a).a,_));return new F(function(){return _14l(_,_18H);});}else{return new F(function(){return _16I(_);});}}},_18I=E(_14f);switch(_18I._){case 0:return new F(function(){return _14j(_,new T1(1,_18I.a));});break;case 1:var _18J=B(A1(_18I.a,_));return new F(function(){return _14j(_,new T1(1,_18J));});break;case 2:var _18K=rMV(E(E(_18I.a).c)),_18L=E(_18K);if(!_18L._){var _18M=new T(function(){return B(A1(_18I.b,new T(function(){return B(_qv(_18L.a));})));});return new F(function(){return _14j(_,new T1(1,_18M));});}else{return new F(function(){return _14j(_,_2o);});}break;default:var _18N=rMV(E(E(_18I.a).c)),_18O=E(_18N);if(!_18O._){var _18P=B(A2(_18I.b,E(_18O.a).a,_));return new F(function(){return _14j(_,new T1(1,_18P));});}else{return new F(function(){return _14j(_,_2o);});}}},_18Q=")",_18R=new T2(1,_18Q,_6),_18S=",",_18T="rgba(",_18U=new T(function(){return toJSStr(_6);}),_18V="rgb(",_18W=function(_18X){var _18Y=E(_18X);if(!_18Y._){var _18Z=jsCat(new T2(1,_18V,new T2(1,new T(function(){return String(_18Y.a);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.b);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.c);}),_18R)))))),E(_18U));return E(_18Z);}else{var _190=jsCat(new T2(1,_18T,new T2(1,new T(function(){return String(_18Y.a);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.b);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.c);}),new T2(1,_18S,new T2(1,new T(function(){return String(_18Y.d);}),_18R)))))))),E(_18U));return E(_190);}},_191=new T(function(){return eval("(function(ctx){ctx.beginPath();})");}),_192="fillStyle",_193=new T(function(){return eval("(function(ctx){ctx.fill();})");}),_194=new T(function(){return eval("(function(e,p,v){e[p] = v;})");}),_195=function(_196,_197){return new T2(1,new T2(0,function(_198,_){var _199=E(_196),_19a=B(_14e(_199.a,_199.b,_199.c,_199.d,_)),_19b=E(_198),_19c=__app3(E(_194),_19b,E(_192),B(_18W(_19a))),_19d=__app1(E(_191),_19b),_19e=B(A3(E(_197).b,_19b,_cm,_)),_19f=__app1(E(_193),_19b);return new F(function(){return _qV(_);});},_7),_14d);},_19g=function(_19h,_19i,_19j,_19k){var _19l=function(_19m,_19n,_19o,_){var _19p=function(_19q,_19r,_19s,_){var _19t=function(_19u,_19v,_19w,_){return new F(function(){return _qx(_19k,function(_19x,_19y,_19z,_){var _19A=E(_19m),_19B=E(_19q),_19C=E(_19y),_19D=E(_19z),_19E=__app4(E(_qX),_19A,_19B,_19C,_19D),_19F=_19A+E(_19u),_19G=E(_uk),_19H=__app4(_19G,_19F,_19B,_19C,_19D),_19I=_19B+E(_19x),_19J=__app4(_19G,_19F,_19I,_19C,_19D),_19K=__app4(_19G,_19A,_19I,_19C,_19D),_19L=__app4(_19G,_19A,_19B,_19C,_19D);return new F(function(){return _qV(_);});},_19v,_19w,_);});};return new F(function(){return _qx(_19j,_19t,_19r,_19s,_);});};return new F(function(){return _qx(_19i,_19p,_19n,_19o,_);});},_19M=function(_19N,_){var _19O=E(_19N),_19P=function(_19Q,_){var _19R=function(_19S,_){var _19T=function(_19U,_){var _19V=function(_19W,_){return new T(function(){var _19X=E(_19U),_19Y=E(_19O.a)-E(_19Q)-_19X/2,_19Z=function(_1a0){var _1a1=E(_19W),_1a2=E(_19O.b)-E(_19S)-_1a1/2;return (_1a2!=0)?(_1a2<=0)? -_1a2<_1a1/2:_1a2<_1a1/2:0<_1a1/2;};if(_19Y!=0){if(_19Y<=0){if( -_19Y>=_19X/2){return false;}else{return B(_19Z(_));}}else{if(_19Y>=_19X/2){return false;}else{return B(_19Z(_));}}}else{if(0>=_19X/2){return false;}else{return B(_19Z(_));}}});};return new F(function(){return _qK(_19k,_19V,_);});};return new F(function(){return _qK(_19j,_19T,_);});};return new F(function(){return _qK(_19i,_19R,_);});};return new F(function(){return _qK(_19h,_19P,_);});};return new T3(0,_19M,function(_rD,_rE,_){return new F(function(){return _qx(_19h,_19l,_rD,_rE,_);});},_7);},_1a3=function(_){var _1a4=B(_146(_));return new T(function(){return E(E(_1a4).b);});},_1a5=new T1(1,_1a3),_1a6=0,_1a7=new T1(0,_1a6),_1a8=new T(function(){var _1a9=B(_19g(_1a7,_1a7,_14c,_1a5));return new T3(0,_1a9.a,_1a9.b,_1a9.c);}),_1aa=1,_1ab=new T1(0,_1aa),_1ac=new T4(0,_1ab,_1ab,_1ab,_1ab),_1ad=new T(function(){return B(_195(_1ac,_1a8));}),_1ae=10,_1af=new T1(0,_6),_1ag=new T1(0,_ah),_1ah=new T(function(){return B(unCStr("head"));}),_1ai=new T(function(){return B(_f4(_1ah));}),_1aj=new T(function(){return eval("(function(ctx){ctx.restore();})");}),_1ak=function(_1al,_){var _1am=__app1(E(_1aj),E(_1al));return new F(function(){return _qV(_);});},_1an=new T2(0,_1ak,_7),_1ao=new T2(1,_1an,_14d),_1ap=function(_1aq){return E(_1ao);},_1ar=new T1(0,_1ap),_1as=new T(function(){return eval("(function(ctx){ctx.clip();})");}),_1at=new T(function(){return eval("(function(ctx){ctx.save();})");}),_1au=function(_1av,_1aw){return new T2(1,new T2(0,function(_1ax,_){var _1ay=E(_1ax),_1az=__app1(E(_1at),_1ay),_1aA=__app1(E(_191),_1ay),_1aB=B(A3(E(_1av).b,_1ay,_cm,_)),_1aC=__app1(E(_1as),_1ay);return new F(function(){return _qV(_);});},_7),new T2(1,new T2(1,_14d,new T1(0,function(_1aD){return E(_1aw);})),_1ar));},_1aE=function(_1aF,_1aG){return new F(function(){return A1(_1aG,new T2(0,_7,_1aF));});},_1aH=function(_1aI,_1aJ,_1aK){return new F(function(){return _1aE(_1aJ,_1aK);});},_1aL=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1aM=new T(function(){return B(err(_1aL));}),_1aN=0,_1aO=0,_1aP=0.15,_1aQ=new T1(0,_1aP),_1aR=1,_1aS=new T1(0,_1aR),_1aT=new T4(0,_1aQ,_1aQ,_1aQ,_1aS),_1aU=new T2(1,_eC,_6),_1aV=2,_1aW=new T1(0,_1aV),_1aX=0.2,_1aY=new T1(0,_1aX),_1aZ=new T4(0,_1a7,_1aS,_1aY,_1aS),_1b0="mplus",_1b1=new T1(0,_1ae),_1b2=function(_1b3,_1b4,_){var _1b5=E(_1b3);switch(_1b5._){case 0:return new F(function(){return A2(_1b4,_1b5.a,_);});break;case 1:var _1b6=B(A1(_1b5.a,_));return new F(function(){return A2(_1b4,_1b6,_);});break;case 2:var _1b7=rMV(E(E(_1b5.a).c)),_1b8=E(_1b7);if(!_1b8._){var _1b9=new T(function(){return B(A1(_1b5.b,new T(function(){return B(_qv(_1b8.a));})));});return new F(function(){return A2(_1b4,_1b9,_);});}else{return _7;}break;default:var _1ba=rMV(E(E(_1b5.a).c)),_1bb=E(_1ba);if(!_1bb._){var _1bc=B(A2(_1b5.b,E(_1bb.a).a,_));return new F(function(){return A2(_1b4,_1bc,_);});}else{return _7;}}},_1bd="lineWidth",_1be="strokeStyle",_1bf=new T(function(){return eval("(function(ctx){ctx.stroke();})");}),_1bg=function(_1bh,_1bi,_1bj){var _1bk=function(_1bl,_){return new F(function(){return _1b2(_1bh,function(_1bm,_){var _1bn=E(_1bi),_1bo=B(_14e(_1bn.a,_1bn.b,_1bn.c,_1bn.d,_)),_1bp=E(_1bl),_1bq=E(_194),_1br=__app3(_1bq,_1bp,E(_1be),B(_18W(_1bo))),_1bs=String(E(_1bm)),_1bt=__app3(_1bq,_1bp,E(_1bd),_1bs),_1bu=__app1(E(_191),_1bp),_1bv=B(A3(E(_1bj).b,_1bp,_5i,_)),_1bw=__app1(E(_1bf),_1bp);return new F(function(){return _qV(_);});},_);});};return new T2(1,new T2(0,_1bk,_7),_14d);},_1bx=function(_1by){var _1bz=E(_1by);if(!_1bz._){return E(_oN);}else{var _1bA=E(_1bz.a),_1bB=E(_1bA.c),_1bC=_1bB.a,_1bD=_1bB.b,_1bE=E(_1bA.d),_1bF=new T(function(){return B(_1bx(_1bz.b));}),_1bG=function(_1bH){return E(_1bF);},_1bI=new T(function(){var _1bJ=new T(function(){var _1bK=new T(function(){return B(A3(_f8,_eY,new T2(1,function(_1bL){return new F(function(){return _fi(0,_1bA.a,_1bL);});},new T2(1,function(_1bM){return new F(function(){return _fi(0,_1bA.b,_1bM);});},_6)),_1aU));}),_1bN=B(_vh(_1b0,new T1(0,new T2(1,_eD,_1bK)),_1aN,_1aO,new T1(0,_1bC),new T1(0,_1bD),_1b1));return new T3(0,_1bN.a,_1bN.b,_1bN.c);});return B(_195(_1aT,_1bJ));}),_1bO=B(_1bg(_1aW,_1aZ,new T(function(){var _1bP=B(_ur(new T2(0,new T1(0,_1bC),new T1(0,_1bD)),new T2(0,new T1(0,_1bE.a),new T1(0,_1bE.b))));return new T3(0,_1bP.a,_1bP.b,_1bP.c);})));if(!_1bO._){var _1bQ=E(_1bI);return (_1bQ._==0)?E(_1bF):new T2(1,_1bQ.a,new T2(1,_1bQ.b,new T1(0,_1bG)));}else{return new T2(1,_1bO.a,new T2(1,new T2(1,_1bO.b,new T1(0,function(_1bR){return E(_1bI);})),new T1(0,_1bG)));}}},_1bS=function(_1bT){var _1bU=E(_1bT);if(!_1bU._){return __Z;}else{var _1bV=E(_1bU.a);return new T2(1,_1bV.a,new T2(1,_1bV.b,new T(function(){return B(_1bS(_1bU.b));})));}},_1bW=new T4(0,_1aS,_1a7,_1a7,_1aS),_1bX=5,_1bY=new T1(0,_1bX),_1bZ=function(_1c0,_1c1){while(1){var _1c2=B((function(_1c3,_1c4){var _1c5=E(_1c4);if(!_1c5._){var _1c6=_1c5.e,_1c7=E(_1c5.b),_1c8=new T(function(){var _1c9=E(_1c5.c);if(_1c9._==1){var _1ca=E(_1c9.a),_1cb=_1ca.a,_1cc=_1ca.b,_1cd=new T(function(){return B(_1bZ(_1c3,_1c6));}),_1ce=function(_1cf){return E(_1cd);},_1cg=new T(function(){var _1ch=new T(function(){var _1ci=new T(function(){return B(A3(_f8,_eY,new T2(1,function(_1cj){return new F(function(){return _fi(0,E(_1c7.a),_1cj);});},new T2(1,function(_1ck){return new F(function(){return _fi(0,E(_1c7.b),_1ck);});},_6)),_1aU));}),_1cl=B(_vh(_1b0,new T1(0,new T2(1,_eD,_1ci)),_1aN,_1aO,new T1(0,new T(function(){return E(_1cb)-10;})),new T1(0,new T(function(){return E(_1cc)-10;})),_1b1));return new T3(0,_1cl.a,_1cl.b,_1cl.c);});return B(_195(_1aT,_1ch));}),_1cm=B(_195(_1bW,new T(function(){var _1cn=B(_qZ(new T1(0,_1cb),new T1(0,_1cc),_1bY));return new T3(0,_1cn.a,_1cn.b,_1cn.c);})));if(!_1cm._){var _1co=E(_1cg);if(!_1co._){return E(_1cd);}else{return new T2(1,_1co.a,new T2(1,_1co.b,new T1(0,_1ce)));}}else{return new T2(1,_1cm.a,new T2(1,new T2(1,_1cm.b,new T1(0,function(_1cp){return E(_1cg);})),new T1(0,_1ce)));}}else{return B(_1bZ(_1c3,_1c6));}},1);_1c0=_1c8;_1c1=_1c5.d;return __continue;}else{return E(_1c3);}})(_1c0,_1c1));if(_1c2!=__continue){return _1c2;}}},_1cq=function(_1cr){return new F(function(){return _fi(0,E(_1cr),_6);});},_1cs=function(_1ct,_1cu){var _1cv=E(_1ct);if(!_1cv._){return E(_1af);}else{var _1cw=E(_1cu);if(!_1cw._){return E(_1af);}else{var _1cx=E(_1cw.a),_1cy=_1cx.a,_1cz=_1cx.b,_1cA=new T(function(){return B(_1cs(_1cv.b,_1cw.b));}),_1cB=function(_1cC){var _1cD=E(_1cA);return (_1cD._==0)?new T1(0,new T2(1,_1cC,_1cD.a)):new T2(1,_1cD.a,new T2(1,_1cD.b,new T1(0,function(_1cE){return new T1(0,new T2(1,_1cC,_1cE));})));},_1cF=new T(function(){var _1cG=new T(function(){var _1cH=B(_vh(_1b0,new T1(0,new T(function(){return B(_1cq(_1cv.a));})),_1aN,_1aO,new T1(0,new T(function(){return E(_1cy)-10;})),new T1(0,new T(function(){return E(_1cz)-10;})),_1b1));return new T3(0,_1cH.a,_1cH.b,_1cH.c);});return B(_195(_1aT,_1cG));}),_1cI=B(_195(_1aT,new T(function(){var _1cJ=B(_qZ(new T1(0,_1cy),new T1(0,_1cz),_1bY));return new T3(0,_1cJ.a,_1cJ.b,_1cJ.c);})));if(!_1cI._){var _1cK=E(_1cF);if(!_1cK._){return new F(function(){return _1cB(_1cK.a);});}else{return new T2(1,_1cK.a,new T2(1,_1cK.b,new T1(0,_1cB)));}}else{return new T2(1,_1cI.a,new T2(1,new T2(1,_1cI.b,new T1(0,function(_1cL){return E(_1cF);})),new T1(0,_1cB)));}}}},_1cM=new T(function(){return B(_Y1(0,2147483647));}),_1cN=function(_1cO){var _1cP=E(_1cO);if(!_1cP._){return __Z;}else{return new F(function(){return _2(B(_1cN(_1cP.a)),new T2(1,_1cP.b,new T(function(){return B(_1cN(_1cP.c));})));});}},_1cQ=function(_1cR,_1cS){return new F(function(){return A1(_1cR,_1cS);});},_1cT=function(_1aJ,_1aK){return new F(function(){return _1cQ(_1aJ,_1aK);});},_1cU=function(_1cV,_1cW){var _1cX=E(E(_1cV).a)-E(E(_1cW).a);return (_1cX!=0)?(_1cX<=0)? -_1cX<5:_1cX<5:true;},_1cY=0.5,_1cZ=new T1(0,_1cY),_1d0=new T4(0,_1a7,_1cZ,_1aS,_1aS),_1d1=function(_1d2,_1d3){var _1d4=E(E(_1d2).a),_1d5=E(E(_1d3).a);return (_1d4>=_1d5)?(_1d4!=_1d5)?2:1:0;},_1d6=new T4(0,_1a6,_1a6,_se,_5i),_1d7=new T2(0,_1a6,_1d6),_1d8=new T2(0,_1d7,_6),_1d9=function(_1da,_1db){var _1dc=E(E(_1da).b)-E(E(_1db).b);return (_1dc!=0)?(_1dc<=0)? -_1dc<5:_1dc<5:true;},_1dd=400,_1de=function(_1df,_1dg,_1dh){var _1di=new T(function(){return new T1(0,B(_p6(_1dg,_1dh,_p4)));}),_1dj=function(_1dk){return new T1(1,new T2(1,new T(function(){return B(A1(_1dk,_7));}),new T2(1,_1di,_6)));};return new F(function(){return A2(_rJ,_1df,_1dj);});},_1dl=function(_1dm,_1dn,_1do,_){var _1dp=__app2(E(_v4),E(_1dn),E(_1do));return new F(function(){return _qV(_);});},_1dq=function(_1dr,_1ds,_1dt,_1du,_1dv,_1dw,_1dx){var _1dy=function(_1dz,_1dA,_1dB,_){var _1dC=function(_1dD,_1dE,_1dF,_){var _1dG=function(_1dH,_1dI,_1dJ,_){var _1dK=function(_1dL,_1dM,_1dN,_){return new F(function(){return _qx(_1dv,function(_1dO,_1dP,_1dQ,_){return new F(function(){return _qx(_1dw,_1dl,_1dP,_1dQ,_);});},_1dM,_1dN,_);});};return new F(function(){return _qx(_1du,_1dK,_1dI,_1dJ,_);});};return new F(function(){return _qx(_1dt,_1dG,_1dE,_1dF,_);});};return new F(function(){return _qx(_1ds,_1dC,_1dA,_1dB,_);});},_1dR=function(_1dS,_){var _1dT=E(_1dS),_1dU=_1dT.a,_1dV=_1dT.b,_1dW=function(_1dX,_){var _1dY=function(_1dZ,_){var _1e0=function(_1e1,_){var _1e2=function(_1e3,_){var _1e4=function(_1e5,_){var _1e6=function(_1e7){var _1e8=new T(function(){return E(_1dZ)*E(_1e3)-E(_1dX)*E(_1e5);});return new F(function(){return A1(_1dx,new T2(0,new T(function(){var _1e9=E(_1dZ),_1ea=E(_1e5);return ( -(_1e9*E(_1e7))+_1e9*E(_1dV)+_1ea*E(_1e1)-_1ea*E(_1dU))/E(_1e8);}),new T(function(){var _1eb=E(_1dX),_1ec=E(_1e3);return (_1eb*E(_1e7)-_1eb*E(_1dV)-_1ec*E(_1e1)+_1ec*E(_1dU))/E(_1e8);})));});};return new F(function(){return _qK(_1dw,_1e6,_);});};return new F(function(){return _qK(_1dv,_1e4,_);});};return new F(function(){return _qK(_1du,_1e2,_);});};return new F(function(){return _qK(_1dt,_1e0,_);});};return new F(function(){return _qK(_1ds,_1dY,_);});};return new F(function(){return _qK(_1dr,_1dW,_);});};return new T3(0,_1dR,function(_rD,_rE,_){return new F(function(){return _qx(_1dr,_1dy,_rD,_rE,_);});},_7);},_1ed=function(_1ee,_1ef,_1eg){var _1eh=E(_1ef),_1ei=E(_1eg);switch(_1ei._){case 0:var _1ej=_1ei.a,_1ek=_1ei.b,_1el=_1ei.c,_1em=_1ei.d,_1en=_1ek>>>0;if(((_1ee>>>0&((_1en-1>>>0^4294967295)>>>0^_1en)>>>0)>>>0&4294967295)==_1ej){return ((_1ee>>>0&_1en)>>>0==0)?new T4(0,_1ej,_1ek,E(B(_1ed(_1ee,_1eh,_1el))),E(_1em)):new T4(0,_1ej,_1ek,E(_1el),E(B(_1ed(_1ee,_1eh,_1em))));}else{var _1eo=(_1ee>>>0^_1ej>>>0)>>>0,_1ep=(_1eo|_1eo>>>1)>>>0,_1eq=(_1ep|_1ep>>>2)>>>0,_1er=(_1eq|_1eq>>>4)>>>0,_1es=(_1er|_1er>>>8)>>>0,_1et=(_1es|_1es>>>16)>>>0,_1eu=(_1et^_1et>>>1)>>>0&4294967295,_1ev=_1eu>>>0;return ((_1ee>>>0&_1ev)>>>0==0)?new T4(0,(_1ee>>>0&((_1ev-1>>>0^4294967295)>>>0^_1ev)>>>0)>>>0&4294967295,_1eu,E(new T2(1,_1ee,_1eh)),E(_1ei)):new T4(0,(_1ee>>>0&((_1ev-1>>>0^4294967295)>>>0^_1ev)>>>0)>>>0&4294967295,_1eu,E(_1ei),E(new T2(1,_1ee,_1eh)));}break;case 1:var _1ew=_1ei.a;if(_1ee!=_1ew){var _1ex=(_1ee>>>0^_1ew>>>0)>>>0,_1ey=(_1ex|_1ex>>>1)>>>0,_1ez=(_1ey|_1ey>>>2)>>>0,_1eA=(_1ez|_1ez>>>4)>>>0,_1eB=(_1eA|_1eA>>>8)>>>0,_1eC=(_1eB|_1eB>>>16)>>>0,_1eD=(_1eC^_1eC>>>1)>>>0&4294967295,_1eE=_1eD>>>0;return ((_1ee>>>0&_1eE)>>>0==0)?new T4(0,(_1ee>>>0&((_1eE-1>>>0^4294967295)>>>0^_1eE)>>>0)>>>0&4294967295,_1eD,E(new T2(1,_1ee,_1eh)),E(_1ei)):new T4(0,(_1ee>>>0&((_1eE-1>>>0^4294967295)>>>0^_1eE)>>>0)>>>0&4294967295,_1eD,E(_1ei),E(new T2(1,_1ee,_1eh)));}else{return new T2(1,_1ee,_1eh);}break;default:return new T2(1,_1ee,_1eh);}},_1eF=6,_1eG=4,_1eH=0,_1eI=2,_1eJ=1,_1eK=3,_1eL=5,_1eM=new T1(0,_ah),_1eN=function(_1eO,_1eP){return new F(function(){return A1(_1eP,new T2(0,_7,_1eO));});},_1eQ=new T1(1,_6),_1eR=0,_1eS=new T4(0,_1eR,_1eR,_se,_5i),_1eT=new T2(0,_1eR,_1eS),_1eU=new T2(0,_1eT,_6),_1eV=1,_1eW=new T4(0,_1eV,_1eV,_se,_5i),_1eX=new T2(0,_1eV,_1eW),_1eY=new T2(0,_1eX,_6),_1eZ=function(_1f0){return E(E(_1f0).c);},_1f1=new T1(1,_6),_1f2=function(_1f3){var _1f4=function(_){var _1f5=nMV(_1f1);return new T(function(){return B(A1(_1f3,_1f5));});};return new T1(0,_1f4);},_1f6=function(_1f7,_1f8){var _1f9=new T(function(){return B(_1eZ(_1f7));}),_1fa=B(_rF(_1f7)),_1fb=function(_1fc){var _1fd=new T(function(){return B(A1(_1f9,new T(function(){return B(A1(_1f8,_1fc));})));});return new F(function(){return A3(_rH,_1fa,_1fd,new T(function(){return B(A2(_b1,_1fa,_1fc));}));});};return new F(function(){return A3(_ap,_1fa,new T(function(){return B(A2(_rJ,_1f7,_1f2));}),_1fb);});},_1fe=function(_1ff,_1fg,_1fh,_1fi){var _1fj=new T(function(){return B(A1(_1ff,_1eI));}),_1fk=new T(function(){return B(A1(_1ff,_1eH));}),_1fl=new T(function(){return B(A1(_1ff,_1eG));}),_1fm=new T(function(){return B(_1f6(_4l,_1fi));}),_1fn=new T(function(){return B(A1(_1ff,_1eF));}),_1fo=new T(function(){return B(A1(_1ff,_1eL));}),_1fp=new T(function(){return B(A1(_1ff,_1eK));}),_1fq=new T(function(){return B(A1(_1ff,_1eJ));}),_1fr=function(_1fs){var _1ft=new T(function(){return B(A1(_1fm,_1fs));}),_1fu=function(_1fv){var _1fw=function(_1fx){var _1fy=E(_1fx),_1fz=_1fy.a,_1fA=_1fy.b,_1fB=new T(function(){var _1fC=E(_1fj);if(!_1fC._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fC.a));}}),_1fD=new T(function(){var _1fE=E(_1fk);if(!_1fE._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fE.a));}}),_1fF=new T(function(){var _1fG=E(_1fl);if(!_1fG._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fG.a));}}),_1fH=new T(function(){var _1fI=E(_1fn);if(!_1fI._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fI.a));}}),_1fJ=new T(function(){var _1fK=E(_1fo);if(!_1fK._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fK.a));}}),_1fL=new T(function(){var _1fM=E(_1fp);if(!_1fM._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fM.a));}}),_1fN=new T(function(){var _1fO=E(_1fq);if(!_1fO._){return E(_1eN);}else{return B(_1de(_4l,_1fz,_1fO.a));}}),_1fP=function(_){var _1fQ=nMV(_1eY),_1fR=_1fQ,_1fS=function(_){var _1fT=nMV(_1eU),_1fU=_1fT,_1fV=function(_){var _1fW=nMV(_1eU),_1fX=_1fW,_1fY=function(_){var _1fZ=nMV(_1eU),_1g0=_1fZ,_1g1=function(_){var _1g2=nMV(_1eY),_1g3=_1g2,_1g4=function(_){var _1g5=nMV(_1eU),_1g6=_1g5,_1g7=function(_1g8,_1g9,_1ga,_1gb,_1gc,_1gd){var _1ge=new T(function(){return B(_tk(_1fR,_1g8));}),_1gf=new T(function(){return B(_tk(_1fU,_1g9));}),_1gg=new T(function(){return B(_tk(_1fX,_1ga));}),_1gh=new T(function(){return B(_tk(_1g0,_1gb));}),_1gi=new T(function(){return B(_tk(_1g3,_1gc));}),_1gj=new T(function(){return B(_tk(_1g6,_1gd));}),_1gk=function(_1gl){var _1gm=new T(function(){return B(A1(_1ge,_1gl));}),_1gn=function(_1go){var _1gp=function(_1gq){return new F(function(){return A1(_1go,new T2(0,_7,E(_1gq).b));});},_1gr=function(_1gs){return new F(function(){return A2(_1gj,E(_1gs).b,_1gp);});},_1gt=function(_1gu){return new F(function(){return A2(_1gi,E(_1gu).b,_1gr);});},_1gv=function(_1gw){return new F(function(){return A2(_1gh,E(_1gw).b,_1gt);});},_1gx=function(_1gy){return new F(function(){return A2(_1gg,E(_1gy).b,_1gv);});};return new F(function(){return A1(_1gm,function(_1gz){return new F(function(){return A2(_1gf,E(_1gz).b,_1gx);});});});};return E(_1gn);};return E(_1gk);},_1gA=new T2(1,new T2(2,_1g7,_7),_1eM),_1gB=new T(function(){var _1gC=E(_1fh);if(!_1gC._){return E(_1gA);}else{return new T2(1,_1gC.a,new T2(1,_1gC.b,new T1(0,function(_1gD){return E(_1gA);})));}}),_1gE=new T(function(){var _1gF=B(_1dq(new T2(2,new T3(0,_tj,_1cQ,_1fR),_2E),new T2(2,new T3(0,_tj,_1cQ,_1fU),_2E),new T2(2,new T3(0,_tj,_1cQ,_1fX),_2E),new T2(2,new T3(0,_tj,_1cQ,_1g0),_2E),new T2(2,new T3(0,_tj,_1cQ,_1g3),_2E),new T2(2,new T3(0,_tj,_1cQ,_1g6),_2E),E(_1fg).a));return new T3(0,_1gF.a,_1gF.b,_1gF.c);}),_1gG=function(_){var _1gH=nMV(_1eQ),_1gI=_1gH,_1gJ=new T(function(){var _1gK=function(_1gL){return new F(function(){return _1gM(E(_1gL).b);});},_1gN=function(_1gO){var _1gP=new T(function(){return B(A2(_1fN,_1gO,_1gQ));}),_1gR=new T(function(){return B(A2(_1fB,_1gO,_1gK));}),_1gS=new T(function(){return B(A2(_1fL,_1gO,_1gT));}),_1gU=new T(function(){return B(_1gN(_1gO));}),_1gV=function(_1gW){var _1gX=E(_1gW);if(!_1gX._){return (!E(_1gX.a))?E(_1gU):E(_1gS);}else{var _1gY=function(_){var _1gZ=B(A2(E(_1gE).a,_1gX.a,_));return new T(function(){if(!E(_1gZ)){return E(_1gR);}else{return E(_1gP);}});};return new T1(0,_1gY);}};return new T1(0,B(_pi(_1gI,_1gV)));},_1gQ=function(_1h0){return new F(function(){return _1gN(E(_1h0).b);});},_1gM=function(_1h1){var _1h2=new T(function(){return B(_1gM(_1h1));}),_1h3=new T(function(){return B(A2(_1fD,_1h1,_1gQ));}),_1h4=function(_1h5){var _1h6=E(_1h5);if(!_1h6._){return E(_1h2);}else{var _1h7=function(_){var _1h8=B(A2(E(_1gE).a,_1h6.a,_));return new T(function(){if(!E(_1h8)){return E(_1h2);}else{return E(_1h3);}});};return new T1(0,_1h7);}};return new T1(0,B(_pi(_1gI,_1h4)));},_1h9=function(_1ha){var _1hb=new T(function(){return B(A2(_1fF,_1ha,_1gT));}),_1hc=new T(function(){return B(A2(_1fB,_1ha,_1hd));}),_1he=new T(function(){return B(_1h9(_1ha));}),_1hf=new T(function(){return B(A2(_1fJ,_1ha,_1gQ));}),_1hg=function(_1hh){var _1hi=E(_1hh);if(!_1hi._){return (!E(_1hi.a))?E(_1hf):E(_1he);}else{var _1hj=function(_){var _1hk=B(A2(E(_1gE).a,_1hi.a,_));return new T(function(){if(!E(_1hk)){return E(_1hc);}else{return E(_1hb);}});};return new T1(0,_1hj);}};return new T1(0,B(_pi(_1gI,_1hg)));},_1gT=function(_1hl){return new F(function(){return _1h9(E(_1hl).b);});},_1hm=function(_1hn){var _1ho=new T(function(){return B(A2(_1fD,_1hn,_1gT));}),_1hp=new T(function(){return B(A2(_1fF,_1hn,_1hd));}),_1hq=new T(function(){return B(_1hm(_1hn));}),_1hr=new T(function(){return B(A2(_1fH,_1hn,_1gK));}),_1hs=function(_1ht){var _1hu=E(_1ht);if(!_1hu._){return (!E(_1hu.a))?E(_1hr):E(_1hq);}else{var _1hv=function(_){var _1hw=B(A2(E(_1gE).a,_1hu.a,_));return new T(function(){if(!E(_1hw)){return E(_1hp);}else{return E(_1ho);}});};return new T1(0,_1hv);}};return new T1(0,B(_pi(_1gI,_1hs)));},_1hd=function(_1hx){return new F(function(){return _1hm(E(_1hx).b);});};return B(_1gM(_1fA));}),_1hy=new T(function(){var _1hz=function(_1hA){var _1hB=E(_1hA);return new F(function(){return A1(_1fv,new T2(0,new T(function(){return new T3(0,E(_1hB.a),_1gB,E(_1fz));}),_1hB.b));});},_1hC=function(_1hD,_1hE,_1hF){var _1hG=new T(function(){return E(E(_1hD).d);}),_1hH=new T(function(){return E(E(_1hG).a);}),_1hI=new T(function(){var _1hJ=E(_1hD);return new T4(0,E(_1hJ.a),_1hJ.b,E(_1hJ.c),E(new T2(0,new T(function(){return E(_1hH)+1|0;}),new T(function(){return B(_1ed(E(_1hH),_1gI,E(_1hG).b));}))));});return new F(function(){return A1(_1hF,new T2(0,new T2(0,_1hH,_1hI),_1hE));});};return B(A(_rS,[_4l,_1fA,_1hC,_1fA,_1hz]));});return new T1(1,new T2(1,_1hy,new T2(1,_1gJ,_6)));};return new T1(0,_1gG);};return new T1(0,_1g4);};return new T1(0,_1g1);};return new T1(0,_1fY);};return new T1(0,_1fV);};return new T1(0,_1fS);};return new T1(0,_1fP);};return new F(function(){return A1(_1ft,_1fw);});};return E(_1fu);};return E(_1fr);},_1hK=function(_1hL,_1hM,_1hN){while(1){var _1hO=E(_1hN);if(!_1hO._){return false;}else{if(!B(A2(_1hL,_1hO.a,_1hM))){_1hN=_1hO.b;continue;}else{return true;}}}},_1hP=function(_1hQ,_1hR){var _1hS=function(_1hT,_1hU){while(1){var _1hV=B((function(_1hW,_1hX){var _1hY=E(_1hW);if(!_1hY._){return __Z;}else{var _1hZ=_1hY.a,_1i0=_1hY.b;if(!B(_1hK(_1hQ,_1hZ,_1hX))){return new T2(1,_1hZ,new T(function(){return B(_1hS(_1i0,new T2(1,_1hZ,_1hX)));}));}else{var _1i1=_1hX;_1hT=_1i0;_1hU=_1i1;return __continue;}}})(_1hT,_1hU));if(_1hV!=__continue){return _1hV;}}};return new F(function(){return _1hS(_1hR,_6);});},_1i2=function(_1i3){return E(E(_1i3).a);},_1i4=function(_1i5){return E(E(_1i5).a);},_1i6=function(_1i7,_1i8,_1i9){var _1ia=E(_1i8),_1ib=E(_1i9),_1ic=new T(function(){var _1id=B(_1i2(_1i7)),_1ie=B(_1i6(_1i7,_1ib,B(A3(_nT,_1id,new T(function(){return B(A3(_1i4,_1id,_1ib,_1ib));}),_1ia))));return new T2(1,_1ie.a,_1ie.b);});return new T2(0,_1ia,_1ic);},_1if=function(_1ig){return E(E(_1ig).b);},_1ih=function(_1ii,_1ij){var _1ik=E(_1ij);if(!_1ik._){return __Z;}else{var _1il=_1ik.a;return (!B(A1(_1ii,_1il)))?__Z:new T2(1,_1il,new T(function(){return B(_1ih(_1ii,_1ik.b));}));}},_1im=function(_1in,_1io,_1ip,_1iq,_1ir){var _1is=B(_1i6(_1io,_1ip,_1iq)),_1it=new T(function(){var _1iu=new T(function(){return B(_1i2(_1io));}),_1iv=new T(function(){return B(A3(_1if,_1io,new T(function(){return B(A3(_nT,_1iu,_1iq,_1ip));}),new T(function(){return B(A2(_d1,_1iu,_jC));})));});if(!B(A3(_zB,_1in,_1iq,_1ip))){var _1iw=new T(function(){return B(A3(_1i4,_1iu,_1ir,_1iv));});return function(_1ix){return new F(function(){return A3(_zB,_1in,_1ix,_1iw);});};}else{var _1iy=new T(function(){return B(A3(_1i4,_1iu,_1ir,_1iv));});return function(_1iz){return new F(function(){return A3(_zz,_1in,_1iz,_1iy);});};}});return new F(function(){return _1ih(_1it,new T2(1,_1is.a,_1is.b));});},_1iA=function(_1iB,_){var _1iC=E(_1iB);if(!_1iC._){return _6;}else{var _1iD=B(A1(_1iC.a,_)),_1iE=B(_1iA(_1iC.b,_));return new T2(1,_1iD,_1iE);}},_1iF=function(_1iG,_1iH){return function(_){var _1iI=B(_146(_)),_1iJ=new T(function(){return E(E(_1iI).b);}),_1iK=new T(function(){return E(_1iJ)+100;}),_1iL=new T(function(){return E(E(_1iI).a)/2;}),_1iM=new T(function(){return E(_1iL)/2;}),_1iN=new T(function(){return E(_1iL)/5+10;}),_1iO=new T(function(){return E(_1iL)/5;}),_1iP=function(_){var _1iQ=function(_){var _1iR=B(_oG(new T2(0,_1a6,_1iL),_)),_1iS=B(_oG(new T2(0,_1a6,_1iJ),_));return new T2(0,_1iR,_1iS);},_1iT=function(_1iU){var _1iV=E(_1iU);return (_1iV==1)?E(new T2(1,_1iQ,_6)):new T2(1,_1iQ,new T(function(){return B(_1iT(_1iV-1|0));}));},_1iW=B(_1iA(B(_1iT(100)),_)),_1iX=new T(function(){return B(_Y7(_Yd,B(_Yg(_1d1,B(_tH(B(_1hP(_1cU,B(_1hP(_1d9,_1iW)))),10))))));}),_1iY=new T(function(){var _1iZ=B(_Z5(_1iX,_1iL,_1iJ));return new T2(0,_1iZ.a,_1iZ.b);}),_1j0=new T(function(){return E(E(_1iY).b);}),_1j1=function(_1j2){var _1j3=E(_1j2);if(!_1j3._){return E(_oN);}else{var _1j4=E(_1j3.a),_1j5=B(_uZ(_1j4,_1j0));if(!_1j5._){return E(_oN);}else{var _1j6=new T(function(){return E(E(_1j5.a).b);}),_1j7=new T(function(){return E(E(_1j6).c);}),_1j8=new T(function(){var _1j9=B(_uK(_1iM,_1iN,_1iO,_1j7)),_1ja=function(_1jb){var _1jc=E(_1jb);if(!_1jc._){return E(_oN);}else{var _1jd=E(_1jc.a),_1je=_1jd.a,_1jf=_1jd.c,_1jg=_1jd.d,_1jh=E(_1jd.b),_1ji=new T(function(){return E(E(_1je).b);}),_1jj=new T(function(){return E(E(_1je).a)+E(_1iL);}),_1jk=new T(function(){return B(_1ja(_1jc.b));}),_1jl=function(_1jm){return E(_1jk);},_1jn=new T(function(){var _1jo=new T(function(){var _1jp=new T(function(){var _1jq=function(_1jr){var _1js=E(_1jf);if(!_1js._){return new T3(0,_5k,_5f,_7);}else{var _1jt=E(_1js.c);if(!_1jt._){return new T3(0,_5k,_5f,_7);}else{var _1ju=new T(function(){var _1jv=E(_1j9);if(!_1jv._){return E(_1ai);}else{var _1jw=_1jv.b,_1jx=E(_1jv.a),_1jy=E(_1jx.b),_1jz=E(_1jt.b),_1jA=E(_1jz.a).a,_1jB=E(_1jz.b).a;if(E(_1jy.a)!=_1jA){var _1jC=function(_1jD){while(1){var _1jE=E(_1jD);if(!_1jE._){return E(_1ai);}else{var _1jF=_1jE.b,_1jG=E(_1jE.a),_1jH=E(_1jG.b);if(E(_1jH.a)!=_1jA){_1jD=_1jF;continue;}else{if(E(_1jH.b)!=_1jB){_1jD=_1jF;continue;}else{return new T4(0,_1jG.a,_1jH,_1jG.c,_1jG.d);}}}}};return E(B(_1jC(_1jw)).a);}else{if(E(_1jy.b)!=_1jB){var _1jI=function(_1jJ){while(1){var _1jK=E(_1jJ);if(!_1jK._){return E(_1ai);}else{var _1jL=_1jK.b,_1jM=E(_1jK.a),_1jN=E(_1jM.b);if(E(_1jN.a)!=_1jA){_1jJ=_1jL;continue;}else{if(E(_1jN.b)!=_1jB){_1jJ=_1jL;continue;}else{return new T4(0,_1jM.a,_1jN,_1jM.c,_1jM.d);}}}}};return E(B(_1jI(_1jw)).a);}else{return E(_1jx.a);}}}}),_1jO=new T(function(){return E(E(_1ju).b);}),_1jP=new T(function(){return E(E(_1ju).a)+E(_1iL);}),_1jQ=new T(function(){return Math.sqrt(Math.pow(E(_1jP)-E(_1jj),2)+Math.pow(E(_1jO)-E(_1ji),2));}),_1jR=new T(function(){return (E(_1jP)-E(_1jj))/E(_1jQ);}),_1jS=new T(function(){return (E(_1jO)-E(_1ji))/E(_1jQ);});return new F(function(){return _ur(new T2(0,new T1(0,new T(function(){return E(_1jj)+E(_1jR)*E(_1jg);})),new T1(0,new T(function(){return E(_1ji)+E(_1jS)*E(_1jg);}))),new T2(0,new T1(0,new T(function(){return E(_1jP)-E(_1jR)*E(_1jg)/2;})),new T1(0,new T(function(){return E(_1jO)-E(_1jS)*E(_1jg)/2;}))));});}}},_1jT=E(_1jf);if(!_1jT._){var _1jU=new T(function(){var _1jV=B(_1jq(_));return new T3(0,_1jV.a,_1jV.b,_1jV.c);});return new T3(0,function(_1jW,_){var _1jX=B(A2(E(_1jU).a,_1jW,_));return _5i;},function(_1jY,_1jZ,_){return new F(function(){return A3(E(_1jU).b,_1jY,_1jZ,_);});},new T(function(){return E(E(_1jU).c);}));}else{var _1k0=E(_1jT.a);if(!_1k0._){var _1k1=new T(function(){var _1k2=B(_1jq(_));return new T3(0,_1k2.a,_1k2.b,_1k2.c);});return new T3(0,function(_1k3,_){var _1k4=B(A2(E(_1k1).a,_1k3,_));return _5i;},function(_1k5,_1k6,_){return new F(function(){return A3(E(_1k1).b,_1k5,_1k6,_);});},new T(function(){return E(E(_1k1).c);}));}else{var _1k7=new T(function(){var _1k8=E(_1j9);if(!_1k8._){return E(_1ai);}else{var _1k9=_1k8.b,_1ka=E(_1k8.a),_1kb=E(_1ka.b),_1kc=E(_1k0.b),_1kd=E(_1kc.a).a,_1ke=E(_1kc.b).a;if(E(_1kb.a)!=_1kd){var _1kf=function(_1kg){while(1){var _1kh=E(_1kg);if(!_1kh._){return E(_1ai);}else{var _1ki=_1kh.b,_1kj=E(_1kh.a),_1kk=E(_1kj.b);if(E(_1kk.a)!=_1kd){_1kg=_1ki;continue;}else{if(E(_1kk.b)!=_1ke){_1kg=_1ki;continue;}else{return new T4(0,_1kj.a,_1kk,_1kj.c,_1kj.d);}}}}};return E(B(_1kf(_1k9)).a);}else{if(E(_1kb.b)!=_1ke){var _1kl=function(_1km){while(1){var _1kn=E(_1km);if(!_1kn._){return E(_1ai);}else{var _1ko=_1kn.b,_1kp=E(_1kn.a),_1kq=E(_1kp.b);if(E(_1kq.a)!=_1kd){_1km=_1ko;continue;}else{if(E(_1kq.b)!=_1ke){_1km=_1ko;continue;}else{return new T4(0,_1kp.a,_1kq,_1kp.c,_1kp.d);}}}}};return E(B(_1kl(_1k9)).a);}else{return E(_1ka.a);}}}}),_1kr=new T(function(){return E(E(_1k7).b);}),_1ks=new T(function(){return E(E(_1k7).a)+E(_1iL);}),_1kt=new T(function(){return Math.sqrt(Math.pow(E(_1ks)-E(_1jj),2)+Math.pow(E(_1kr)-E(_1ji),2));}),_1ku=new T(function(){return (E(_1ks)-E(_1jj))/E(_1kt);}),_1kv=new T(function(){return (E(_1kr)-E(_1ji))/E(_1kt);}),_1kw=B(_ur(new T2(0,new T1(0,new T(function(){return E(_1jj)+E(_1ku)*E(_1jg);})),new T1(0,new T(function(){return E(_1ji)+E(_1kv)*E(_1jg);}))),new T2(0,new T1(0,new T(function(){return E(_1ks)-E(_1ku)*E(_1jg)/2;})),new T1(0,new T(function(){return E(_1kr)-E(_1kv)*E(_1jg)/2;}))))),_1kx=new T(function(){var _1ky=B(_1jq(_));return new T3(0,_1ky.a,_1ky.b,_1ky.c);}),_1kz=function(_1kA,_){var _1kB=B(A2(_1kw.a,_1kA,_)),_1kC=B(A2(E(_1kx).a,_1kA,_));return new T(function(){return B(_13X(_1kB,_1kC));});};return new T3(0,_1kz,function(_1kD,_1kE,_){var _1kF=B(A3(_1kw.b,_1kD,_1kE,_));return new F(function(){return A3(E(_1kx).b,_1kD,_1kE,_);});},new T(function(){return E(E(_1kx).c);}));}}});return B(_1bg(_1aW,_1aT,_1jp));}),_1kG=new T(function(){var _1kH=E(_1jg),_1kI=_1kH/2,_1kJ=new T(function(){return B(A3(_f8,_eY,new T2(1,function(_1kK){return new F(function(){return _fi(0,E(_1jh.a),_1kK);});},new T2(1,function(_1kL){return new F(function(){return _fi(0,E(_1jh.b),_1kL);});},_6)),_1aU));});if(_1kI<=10){var _1kM=B(_vh(_1b0,new T1(0,new T2(1,_eD,_1kJ)),_140,_143,new T1(0,new T(function(){return E(_1jj)+_1kH+15;})),new T1(0,_1ji),new T1(0,new T(function(){if(_1kI>10){return _1kI;}else{return E(_1ae);}}))));return new T3(0,_1kM.a,_1kM.b,_1kM.c);}else{var _1kN=B(_vh(_1b0,new T1(0,new T2(1,_eD,_1kJ)),_140,_143,new T1(0,_1jj),new T1(0,_1ji),new T1(0,new T(function(){if(_1kI>10){return _1kI;}else{return E(_1ae);}}))));return new T3(0,_1kN.a,_1kN.b,_1kN.c);}}),_1kO=B(_195(_1aT,_1kG));if(!_1kO._){return E(_1jo);}else{return new T2(1,_1kO.a,new T2(1,_1kO.b,new T1(0,function(_1kP){return E(_1jo);})));}}),_1kQ=B(_1bg(_1aW,_1aT,new T(function(){var _1kR=B(_qZ(new T1(0,_1jj),new T1(0,_1ji),new T1(0,_1jg)));return new T3(0,_1kR.a,_1kR.b,_1kR.c);})));if(!_1kQ._){var _1kS=E(_1jn);return (_1kS._==0)?E(_1jk):new T2(1,_1kS.a,new T2(1,_1kS.b,new T1(0,_1jl)));}else{return new T2(1,_1kQ.a,new T2(1,new T2(1,_1kQ.b,new T1(0,function(_1kT){return E(_1jn);})),new T1(0,_1jl)));}}};return B(_1ja(_1j9));}),_1kU=new T(function(){var _1kV=E(_1j6),_1kW=new T(function(){var _1kX=new T(function(){var _1kY=new T(function(){var _1kZ=new T(function(){return B(_1hP(_5m,B(_1bS(B(_1cN(_1j7))))));}),_1l0=new T(function(){return B(_tR(_1kZ,0))-1|0;}),_1l1=function(_1l2,_1l3){var _1l4=E(_1l2);if(!_1l4._){return E(_1af);}else{var _1l5=E(_1l3);if(!_1l5._){return E(_1af);}else{var _1l6=E(_1l5.a),_1l7=_1l6.b,_1l8=_1l6.c,_1l9=new T(function(){return B(_1l1(_1l4.b,_1l5.b));}),_1la=function(_1lb){var _1lc=E(_1l9);return (_1lc._==0)?new T1(0,new T2(1,_1lb,_1lc.a)):new T2(1,_1lc.a,new T2(1,_1lc.b,new T1(0,function(_1ld){return new T1(0,new T2(1,_1lb,_1ld));})));};if(_1l8>_1j4){return new F(function(){return _1la(_7);});}else{var _1le=E(_1l4.a),_1lf=function(_1lg,_1lh){var _1li=E(_1l0),_1lj=function(_1lk,_1ll){var _1lm=new T(function(){return _1lk<=_1lg;}),_1ln=function(_1lo){var _1lp=function(_1lq){var _1lr=E(_1lq);if(!_1lr._){return E(_oN);}else{var _1ls=E(_1lr.a),_1lt=new T(function(){return B(_1lp(_1lr.b));}),_1lu=function(_1lv){return E(_1lt);},_1lw=function(_1lx,_1ly){var _1lz=(_1l7*_1l7-(_1l7+_1l7)*_1lx+_1l8*_1l8-_1j4*_1j4+_1lx*_1lx)/(_1l8+_1l8-(_1j4+_1j4));if(_1lz<0){return E(_oN);}else{if(_1lz>E(_1iJ)){return E(_oN);}else{var _1lA=new T(function(){var _1lB=_1ls+_1lo,_1lC=new T(function(){if(_1lB>_1lk){if(!E(_1lm)){return E(_1ll);}else{return E(_1lh);}}else{if(_1lB>_1lg){return _1lB;}else{return E(_1lh);}}}),_1lD=B(_ur(new T2(0,new T1(0,_1ly),new T1(0,_1lz)),new T2(0,new T1(0,_1lC),new T1(0,new T(function(){var _1lE=E(_1lC);return (_1l7*_1l7-(_1l7+_1l7)*_1lE+_1l8*_1l8-_1j4*_1j4+_1lE*_1lE)/(_1l8+_1l8-(_1j4+_1j4));})))));return new T3(0,_1lD.a,_1lD.b,_1lD.c);});return new F(function(){return _1bg(_1aW,_1d0,_1lA);});}}};if(_1ls>_1lk){if(!E(_1lm)){var _1lF=B(_1lw(_1lk,_1ll));return (_1lF._==0)?E(_1lt):new T2(1,_1lF.a,new T2(1,_1lF.b,new T1(0,_1lu)));}else{var _1lG=B(_1lw(_1lg,_1lh));return (_1lG._==0)?E(_1lt):new T2(1,_1lG.a,new T2(1,_1lG.b,new T1(0,_1lu)));}}else{if(_1ls>_1lg){var _1lH=B(_1lw(_1ls,_1ls));return (_1lH._==0)?E(_1lt):new T2(1,_1lH.a,new T2(1,_1lH.b,new T1(0,_1lu)));}else{var _1lI=B(_1lw(_1lg,_1lh));return (_1lI._==0)?E(_1lt):new T2(1,_1lI.a,new T2(1,_1lI.b,new T1(0,_1lu)));}}}},_1lJ=B(_1lp(B(_1im(_bP,_a8,_1lh,_1lg+_1lo,_1ll))));if(!_1lJ._){return new F(function(){return _1la(_1lJ.a);});}else{return new T2(1,_1lJ.a,new T2(1,_1lJ.b,new T1(0,_1la)));}};if((_1lk-_1lg)/15<=20){return new F(function(){return _1ln((_1lk-_1lg)/15);});}else{return new F(function(){return _1ln((_1lk-_1lg)/50);});}};if(_1le>=_1li){var _1lK=E(_1iL);return new F(function(){return _1lj(_1lK,_1lK);});}else{if(_1le>=_1li){return E(_1aM);}else{var _1lL=B(_oZ(_1kZ,_1le+1|0)),_1lM=_1lL.b,_1lN=_1lL.c,_1lO=_1l8-_1lN;if(_1lO!=0){if(_1lO<=0){if( -_1lO>=1.0e-7){var _1lP=(_1l8*_1lM+Math.sqrt(((_1l7-_1lM)*(_1l7-_1lM)+_1lO*_1lO)*(_1l8-_1j4)*(_1lN-_1j4))+(_1l7*(_1j4-_1lN)-_1lM*_1j4))/_1lO;return new F(function(){return _1lj(_1lP,_1lP);});}else{var _1lQ=(_1l7+_1lM)/2;return new F(function(){return _1lj(_1lQ,_1lQ);});}}else{if(_1lO>=1.0e-7){var _1lR=(_1l8*_1lM+Math.sqrt(((_1l7-_1lM)*(_1l7-_1lM)+_1lO*_1lO)*(_1l8-_1j4)*(_1lN-_1j4))+(_1l7*(_1j4-_1lN)-_1lM*_1j4))/_1lO;return new F(function(){return _1lj(_1lR,_1lR);});}else{var _1lS=(_1l7+_1lM)/2;return new F(function(){return _1lj(_1lS,_1lS);});}}}else{var _1lT=(_1l7+_1lM)/2;return new F(function(){return _1lj(_1lT,_1lT);});}}}};if(_1le<=0){return new F(function(){return _1lf(0,0);});}else{var _1lU=B(_oZ(_1kZ,_1le-1|0)),_1lV=_1lU.b,_1lW=_1lU.c,_1lX=_1lW-_1l8;if(_1lX!=0){if(_1lX<=0){if( -_1lX>=1.0e-7){var _1lY=(_1lW*_1l7+Math.sqrt(((_1lV-_1l7)*(_1lV-_1l7)+_1lX*_1lX)*(_1lW-_1j4)*(_1l8-_1j4))+(_1lV*(_1j4-_1l8)-_1l7*_1j4))/_1lX;return new F(function(){return _1lf(_1lY,_1lY);});}else{var _1lZ=(_1lV+_1l7)/2;return new F(function(){return _1lf(_1lZ,_1lZ);});}}else{if(_1lX>=1.0e-7){var _1m0=(_1lW*_1l7+Math.sqrt(((_1lV-_1l7)*(_1lV-_1l7)+_1lX*_1lX)*(_1lW-_1j4)*(_1l8-_1j4))+(_1lV*(_1j4-_1l8)-_1l7*_1j4))/_1lX;return new F(function(){return _1lf(_1m0,_1m0);});}else{var _1m1=(_1lV+_1l7)/2;return new F(function(){return _1lf(_1m1,_1m1);});}}}else{var _1m2=(_1lV+_1l7)/2;return new F(function(){return _1lf(_1m2,_1m2);});}}}}}};return B(_1l1(_1cM,_1kZ));});return B(_aY(_7,_1kY));});if(!E(_1kV.a)){return E(_1kX);}else{var _1m3=E(_1kV.d),_1m4=B(_oZ(_1iX,E(_1m3.a))),_1m5=B(_oZ(_1iX,E(_1m3.b))),_1m6=B(_oZ(_1iX,E(_1m3.c))),_1m7=E(_1m4.a),_1m8=E(_1m4.b),_1m9=E(_1m6.a)-_1m7,_1ma=E(_1m6.b)-_1m8,_1mb=E(_1m5.a)-_1m7,_1mc=E(_1m5.b)-_1m8,_1md=_1mb*_1ma-_1mc*_1m9+(_1mb*_1ma-_1mc*_1m9);if(_1md>0){var _1me=new T(function(){var _1mf=_1m9*_1m9+_1ma*_1ma,_1mg=_1mb*_1mb+_1mc*_1mc,_1mh=new T(function(){return _1m7+(_1ma*_1mg-_1mc*_1mf)/_1md;}),_1mi=new T(function(){return _1m8+(_1mb*_1mf-_1m9*_1mg)/_1md;}),_1mj=B(_qZ(new T1(0,_1mh),new T1(0,_1mi),new T1(0,new T(function(){var _1mk=E(_1mh),_1ml=E(_1mi);return Math.sqrt((_1mk-_1m7)*(_1mk-_1m7)+(_1ml-_1m8)*(_1ml-_1m8));}))));return new T3(0,_1mj.a,_1mj.b,_1mj.c);}),_1mm=B(_1bg(_1aW,_1bW,_1me));if(!_1mm._){return E(_1kX);}else{return new T2(1,_1mm.a,new T2(1,_1mm.b,new T1(0,function(_1mn){return E(_1kX);})));}}else{return E(_1kX);}}}),_1mo=B(_1bZ(_oN,_1kV.b));if(!_1mo._){return E(_1kW);}else{return new T2(1,_1mo.a,new T2(1,_1mo.b,new T1(0,function(_1mp){return E(_1kW);})));}}),_1mq=B(_1au(_1a8,_1kU));return (_1mq._==0)?E(_1j8):new T2(1,_1mq.a,new T2(1,_1mq.b,new T1(0,function(_1mr){return E(_1j8);})));}}},_1ms=new T(function(){return B(_1au(_1a8,new T(function(){return B(_1bx(E(_1iY).a));})));}),_1mt=function(_){var _1mu=nMV(_1d8),_1mv=_1mu;return new T(function(){var _1mw=new T(function(){return B(_sp(_bc,_1dd,_1cT,_1mv,_1iK,_1aH));}),_1mx=new T(function(){return B(_tk(_1mv,_1a6));}),_1my=function(_1mz){return new F(function(){return _sp(_bc,_1dd,_1cT,_1mv,_1iK,function(_1mA){return E(_1mz);});});},_1mB=function(_1mC){return new F(function(){return _1mD(E(_1mC).b);});},_1mE=function(_1mF){return new F(function(){return A2(_1mx,E(_1mF).b,_1mB);});},_1mG=function(_1mH){return new T1(0,B(_qf(_1my,E(_1mH).b,_1mE)));},_1mD=function(_1mI){return new F(function(){return A2(_1mw,_1mI,_1mG);});},_1mJ=function(_1mK,_1mL,_1mM){return new T1(1,new T2(1,new T(function(){return B(A1(_1mM,new T2(0,_7,_1mL)));}),new T2(1,new T(function(){return B(_1mD(_1mL));}),_6)));},_1mN=new T(function(){var _1mO=new T(function(){var _1mP=new T(function(){var _1mQ=function(_){var _1mR=rMV(_1mv),_1mS=E(_1mR);return (_1mS._==0)?new T1(1,new T(function(){return B(_qv(_1mS.a));})):_2o;},_1mT=new T2(1,new T1(1,_1mQ),new T2(1,new T2(1,_1ag,new T1(0,_1j1)),new T1(0,function(_1mU){return E(_1ms);}))),_1mV=B(_1bg(_1aW,_1aT,new T(function(){var _1mW=new T3(0,_1dd,_1cT,_1mv),_1mX=B(_ur(new T2(0,_1a7,new T2(2,_1mW,_2E)),new T2(0,_14c,new T2(2,_1mW,_2E))));return new T3(0,_1mX.a,_1mX.b,_1mX.c);})));if(!_1mV._){return E(_1mT);}else{return new T2(1,_1mV.a,new T2(1,_1mV.b,new T1(0,function(_1mY){return E(_1mT);})));}}),_1mZ=B(_aY(_7,new T(function(){return B(_1cs(_1cM,_1iX));})));if(!_1mZ._){return E(_1mP);}else{return new T2(1,_1mZ.a,new T2(1,_1mZ.b,new T1(0,function(_1n0){return E(_1mP);})));}}),_1n1=E(_1ad);if(!_1n1._){return E(_1mO);}else{return new T2(1,_1n1.a,new T2(1,_1n1.b,new T1(0,function(_1n2){return E(_1mO);})));}});return B(A(_1fe,[_141,_1a8,_1mN,_1mJ,_1iG,_1iH]));});};return new T1(0,_1mt);};return new T1(0,_1iP);};},_1n3=function(_1n4,_1n5,_1n6){return new F(function(){return A1(_1n6,new T2(0,new T2(0,_1n4,_1n4),_1n5));});},_1n7=0,_1n8=function(_1n9,_1na){var _1nb=E(_1n9);if(!_1nb._){return new F(function(){return A1(_1nb.a,_1na);});}else{var _1nc=function(_1nd,_1ne){while(1){var _1nf=E(_1nd);if(!_1nf._){var _1ng=B(A1(_1nf.a,_1na));if(!_1ng._){return new F(function(){return _1n8(_1ne,_1ng.a);});}else{return new T2(1,_1ng.a,new T2(1,_1ng.b,_1ne));}}else{var _1nh=new T2(1,_1nf.b,_1ne);_1nd=_1nf.a;_1ne=_1nh;continue;}}};return new F(function(){return _1nc(_1nb.a,_1nb.b);});}},_1ni=function(_1nj,_1nk,_1nl){var _1nm=function(_){var _1nn=B(A1(_1nj,_));return new T(function(){return B(A1(_1nl,new T2(0,_1nn,_1nk)));});};return new T1(0,_1nm);},_1no=function(_1np,_1nq,_1nr){var _1ns=E(_1np);switch(_1ns._){case 0:return new F(function(){return A1(_1nr,new T2(0,_1ns.a,_1nq));});break;case 1:return new F(function(){return _1ni(_1ns.a,_1nq,_1nr);});break;case 2:var _1nt=E(_1ns.a).c,_1nu=function(_1nv){var _1nw=new T(function(){var _1nx=new T(function(){return B(A1(_1ns.b,new T(function(){return B(_qv(_1nv));})));});return B(A1(_1nr,new T2(0,_1nx,_1nq)));});return new T1(0,B(_p6(_1nt,_1nv,function(_1ny){return E(_1nw);})));};return new T1(0,B(_pi(_1nt,_1nu)));default:var _1nz=E(_1ns.a).c,_1nA=function(_1nB){var _1nC=function(_){var _1nD=B(A2(_1ns.b,new T(function(){return B(_qv(_1nB));}),_));return new T(function(){return B(A1(_1nr,new T2(0,_1nD,_1nq)));});};return new T1(0,B(_p6(_1nz,_1nB,function(_1nE){return E(new T1(0,_1nC));})));};return new T1(0,B(_pi(_1nz,_1nA)));}},_1nF=function(_1nG,_1nH,_1nI,_1nJ,_1nK,_1nL,_1nM){while(1){var _1nN=B((function(_1nO,_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU){var _1nV=new T(function(){return 0*E(_1nP)+0*E(_1nQ)+E(_1nR);}),_1nW=new T(function(){return 0*E(_1nS)+0*E(_1nT)+E(_1nU);}),_1nX=E(_1nO);if(!_1nX._){return function(_az,_aA){return new F(function(){return _3Q(_1nX.a,_az,_aA);});};}else{var _1nY=_1nX.b,_1nZ=E(_1nX.a);switch(_1nZ._){case 0:var _1o0=_1nP,_1o1=_1nQ,_1o2=_1nR,_1o3=_1nS,_1o4=_1nT,_1o5=_1nU;_1nG=B(_1n8(_1nY,_1nZ.b));_1nH=_1o0;_1nI=_1o1;_1nJ=_1o2;_1nK=_1o3;_1nL=_1o4;_1nM=_1o5;return __continue;case 1:var _1o6=function(_1o7,_1o8){var _1o9=function(_){var _1oa=B(A1(_1nZ.a,_));return new T(function(){return B(A(_1nF,[B(_1n8(_1nY,_1oa)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU,_1o7,_1o8]));});};return new T1(0,_1o9);};return E(_1o6);case 2:var _1ob=new T(function(){return B(A(_1nZ.a,[_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU]));}),_1oc=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.b)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1od=function(_1oe){var _1of=new T(function(){return B(A1(_1ob,_1oe));}),_1og=function(_1oh){return new F(function(){return A1(_1of,function(_1oi){return new F(function(){return A2(_1oc,E(_1oi).b,_1oh);});});});};return E(_1og);};return E(_1od);case 3:var _1oj=new T(function(){return B(_1nF(_1nZ.b,_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1ok=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.c)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1ol=function(_1om){var _1on=new T(function(){return B(A1(_1oj,_1om));}),_1oo=function(_1op){return new F(function(){return A1(_1on,function(_1oq){return new F(function(){return A2(_1ok,E(_1oq).b,_1op);});});});};return E(_1oo);};return E(_1ol);case 4:var _1or=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.h)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1os=function(_1ot,_1ou){var _1ov=function(_1ow){return new F(function(){return A2(_1or,E(_1ow).b,_1ou);});},_1ox=function(_1oy){var _1oz=E(_1oy),_1oA=_1oz.a,_1oB=function(_1oC){var _1oD=E(_1oC),_1oE=_1oD.a,_1oF=function(_1oG){var _1oH=E(_1oG),_1oI=_1oH.a,_1oJ=function(_1oK){var _1oL=E(_1oK),_1oM=_1oL.a,_1oN=new T(function(){return E(_1oA)*E(_1nS)+E(_1oM)*E(_1nT);}),_1oO=new T(function(){return E(_1oA)*E(_1nP)+E(_1oM)*E(_1nQ);}),_1oP=function(_1oQ){var _1oR=E(_1oQ),_1oS=_1oR.a,_1oT=new T(function(){return E(_1oE)*E(_1nS)+E(_1oS)*E(_1nT);}),_1oU=new T(function(){return E(_1oE)*E(_1nP)+E(_1oS)*E(_1nQ);}),_1oV=function(_1oW){var _1oX=E(_1oW),_1oY=_1oX.a;return new F(function(){return A(_1nF,[_1nZ.g,_1oO,_1oU,new T(function(){return E(_1oI)*E(_1nP)+E(_1oY)*E(_1nQ)+E(_1nR);}),_1oN,_1oT,new T(function(){return E(_1oI)*E(_1nS)+E(_1oY)*E(_1nT)+E(_1nU);}),_1oX.b,_1ov]);});};return new F(function(){return _1no(_1nZ.f,_1oR.b,_1oV);});};return new F(function(){return _1no(_1nZ.e,_1oL.b,_1oP);});};return new F(function(){return _1no(_1nZ.d,_1oH.b,_1oJ);});};return new F(function(){return _1no(_1nZ.c,_1oD.b,_1oF);});};return new F(function(){return _1no(_1nZ.b,_1oz.b,_1oB);});};return new F(function(){return _1no(_1nZ.a,_1ot,_1ox);});};return E(_1os);case 5:var _1oZ=E(_1nZ.a),_1p0=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.c)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1p1=new T(function(){return 0*E(_1nS)+E(_1nT);}),_1p2=new T(function(){return E(_1nS)+0*E(_1nT);}),_1p3=new T(function(){return 0*E(_1nP)+E(_1nQ);}),_1p4=new T(function(){return E(_1nP)+0*E(_1nQ);}),_1p5=function(_1p6,_1p7){var _1p8=function(_1p9){return new F(function(){return A2(_1p0,E(_1p9).b,_1p7);});},_1pa=function(_1pb){var _1pc=E(_1pb),_1pd=_1pc.a,_1pe=function(_1pf){var _1pg=E(_1pf),_1ph=_1pg.a;return new F(function(){return A(_1nF,[_1nZ.b,_1p4,_1p3,new T(function(){return E(_1pd)*E(_1nP)+E(_1ph)*E(_1nQ)+E(_1nR);}),_1p2,_1p1,new T(function(){return E(_1pd)*E(_1nS)+E(_1ph)*E(_1nT)+E(_1nU);}),_1pg.b,_1p8]);});};return new F(function(){return _1no(_1oZ.b,_1pc.b,_1pe);});};return new F(function(){return _1no(_1oZ.a,_1p6,_1pa);});};return E(_1p5);case 6:var _1pi=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.c)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1pj=function(_1pk,_1pl){var _1pm=function(_1pn){return new F(function(){return A2(_1pi,E(_1pn).b,_1pl);});},_1po=function(_1pp){var _1pq=E(_1pp),_1pr=_1pq.a,_1ps=new T(function(){return Math.cos(E(_1pr));}),_1pt=new T(function(){return Math.sin(E(_1pr));}),_1pu=new T(function(){return  -E(_1pt);});return new F(function(){return A(_1nF,[_1nZ.b,new T(function(){return E(_1ps)*E(_1nP)+E(_1pt)*E(_1nQ);}),new T(function(){return E(_1pu)*E(_1nP)+E(_1ps)*E(_1nQ);}),_1nV,new T(function(){return E(_1ps)*E(_1nS)+E(_1pt)*E(_1nT);}),new T(function(){return E(_1pu)*E(_1nS)+E(_1ps)*E(_1nT);}),_1nW,_1pq.b,_1pm]);});};return new F(function(){return _1no(_1nZ.a,_1pk,_1po);});};return E(_1pj);case 7:var _1pv=E(_1nZ.a),_1pw=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.c)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1px=function(_1py,_1pz){var _1pA=function(_1pB){return new F(function(){return A2(_1pw,E(_1pB).b,_1pz);});},_1pC=function(_1pD){var _1pE=E(_1pD),_1pF=_1pE.a,_1pG=new T(function(){return E(_1pF)*E(_1nS)+0*E(_1nT);}),_1pH=new T(function(){return E(_1pF)*E(_1nP)+0*E(_1nQ);}),_1pI=function(_1pJ){var _1pK=E(_1pJ),_1pL=_1pK.a;return new F(function(){return A(_1nF,[_1nZ.b,_1pH,new T(function(){return 0*E(_1nP)+E(_1pL)*E(_1nQ);}),_1nV,_1pG,new T(function(){return 0*E(_1nS)+E(_1pL)*E(_1nT);}),_1nW,_1pK.b,_1pA]);});};return new F(function(){return _1no(_1pv.b,_1pE.b,_1pI);});};return new F(function(){return _1no(_1pv.a,_1py,_1pC);});};return E(_1px);default:var _1pM=new T(function(){return B(_1nF(_1nZ.b,_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1pN=new T(function(){return B(_1nF(B(_1n8(_1nY,_1nZ.c)),_1nP,_1nQ,_1nR,_1nS,_1nT,_1nU));}),_1pO=function(_1pP){var _1pQ=new T(function(){return B(A1(_1pM,_1pP));}),_1pR=function(_1pS){return new F(function(){return A1(_1pQ,function(_1pT){return new F(function(){return A2(_1pN,E(_1pT).b,_1pS);});});});};return E(_1pR);};return E(_1pO);}}})(_1nG,_1nH,_1nI,_1nJ,_1nK,_1nL,_1nM));if(_1nN!=__continue){return _1nN;}}},_1pU=new T(function(){return eval("(function(e){e.width = e.width;})");}),_1pV=1,_1pW=new T1(1,_6),_1pX=new T(function(){return eval("(function(ctx,a,b,c,d,e,f){ctx.transform(a,d,b,e,c,f);})");}),_1pY=new T(function(){return eval("(function(ctx,x,y){ctx.translate(x,y);})");}),_1pZ=new T(function(){return eval("(function(ctx,rad){ctx.rotate(rad);})");}),_1q0=new T(function(){return eval("(function(ctx,x,y){ctx.scale(x,y);})");}),_1q1=function(_1q2,_1q3,_){while(1){var _1q4=B((function(_1q5,_1q6,_){var _1q7=E(_1q5);if(!_1q7._){return _1q7.a;}else{var _1q8=_1q7.b,_1q9=E(_1q7.a);switch(_1q9._){case 0:var _1qa=B(A2(_1q9.a,_1q6,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1q9.b));_1q3=_1qb;return __continue;case 1:var _1qc=B(A1(_1q9.a,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qc));_1q3=_1qb;return __continue;case 2:var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1q9.b));_1q3=_1qb;return __continue;case 3:var _1qd=B(_1q1(_1q9.b,_1q9.a,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1q9.c));_1q3=_1qb;return __continue;case 4:var _1qe=_1q9.h,_1qf=function(_1qg,_){var _1qh=function(_1qi,_){var _1qj=function(_1qk,_){var _1ql=function(_1qm,_){var _1qn=function(_1qo,_){return new F(function(){return _1b2(_1q9.f,function(_1qp,_){var _1qq=E(_1q6),_1qr=__app1(E(_1at),_1qq),_1qs=__apply(E(_1pX),new T2(1,E(_1qp),new T2(1,E(_1qo),new T2(1,E(_1qm),new T2(1,E(_1qk),new T2(1,E(_1qi),new T2(1,E(_1qg),new T2(1,_1qq,_6)))))))),_1qt=B(_1q1(_1q9.g,_1qq,_)),_1qu=__app1(E(_1aj),_1qq);return new F(function(){return _qV(_);});},_);});};return new F(function(){return _1b2(_1q9.e,_1qn,_);});};return new F(function(){return _1b2(_1q9.d,_1ql,_);});};return new F(function(){return _1b2(_1q9.c,_1qj,_);});};return new F(function(){return _1b2(_1q9.b,_1qh,_);});},_1qv=E(_1q9.a);switch(_1qv._){case 0:var _1qw=B(_1qf(_1qv.a,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qe));_1q3=_1qb;return __continue;case 1:var _1qx=B(A1(_1qv.a,_)),_1qy=B(_1qf(_1qx,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qe));_1q3=_1qb;return __continue;case 2:var _1qz=rMV(E(E(_1qv.a).c)),_1qA=E(_1qz);if(!_1qA._){var _1qB=new T(function(){return B(A1(_1qv.b,new T(function(){return B(_qv(_1qA.a));})));},1),_1qC=B(_1qf(_1qB,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qe));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1qe));_1q3=_1qb;return __continue;}break;default:var _1qD=rMV(E(E(_1qv.a).c)),_1qE=E(_1qD);if(!_1qE._){var _1qF=B(A2(_1qv.b,E(_1qE.a).a,_)),_1qG=B(_1qf(_1qF,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qe));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1qe));_1q3=_1qb;return __continue;}}break;case 5:var _1qH=_1q9.c,_1qI=E(_1q9.a),_1qJ=function(_1qK,_){return new F(function(){return _1b2(_1qI.b,function(_1qL,_){var _1qM=E(_1q6),_1qN=__app1(E(_1at),_1qM),_1qO=__app3(E(_1pY),_1qM,E(_1qK),E(_1qL)),_1qP=B(_1q1(_1q9.b,_1qM,_)),_1qQ=__app1(E(_1aj),_1qM);return new F(function(){return _qV(_);});},_);});},_1qR=E(_1qI.a);switch(_1qR._){case 0:var _1qS=B(_1qJ(_1qR.a,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qH));_1q3=_1qb;return __continue;case 1:var _1qT=B(A1(_1qR.a,_)),_1qU=B(_1qJ(_1qT,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qH));_1q3=_1qb;return __continue;case 2:var _1qV=rMV(E(E(_1qR.a).c)),_1qW=E(_1qV);if(!_1qW._){var _1qX=new T(function(){return B(A1(_1qR.b,new T(function(){return B(_qv(_1qW.a));})));},1),_1qY=B(_1qJ(_1qX,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qH));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1qH));_1q3=_1qb;return __continue;}break;default:var _1qZ=rMV(E(E(_1qR.a).c)),_1r0=E(_1qZ);if(!_1r0._){var _1r1=B(A2(_1qR.b,E(_1r0.a).a,_)),_1r2=B(_1qJ(_1r1,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1qH));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1qH));_1q3=_1qb;return __continue;}}break;case 6:var _1r3=_1q9.c,_1r4=function(_1r5,_){var _1r6=E(_1q6),_1r7=__app1(E(_1at),_1r6),_1r8=__app2(E(_1pZ),_1r6,E(_1r5)),_1r9=B(_1q1(_1q9.b,_1r6,_)),_1ra=__app1(E(_1aj),_1r6);return new F(function(){return _qV(_);});},_1rb=E(_1q9.a);switch(_1rb._){case 0:var _1rc=B(_1r4(_1rb.a,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1r3));_1q3=_1qb;return __continue;case 1:var _1rd=B(A1(_1rb.a,_)),_1re=B(_1r4(_1rd,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1r3));_1q3=_1qb;return __continue;case 2:var _1rf=rMV(E(E(_1rb.a).c)),_1rg=E(_1rf);if(!_1rg._){var _1rh=new T(function(){return B(A1(_1rb.b,new T(function(){return B(_qv(_1rg.a));})));},1),_1ri=B(_1r4(_1rh,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1r3));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1r3));_1q3=_1qb;return __continue;}break;default:var _1rj=rMV(E(E(_1rb.a).c)),_1rk=E(_1rj);if(!_1rk._){var _1rl=B(A2(_1rb.b,E(_1rk.a).a,_)),_1rm=B(_1r4(_1rl,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1r3));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1r3));_1q3=_1qb;return __continue;}}break;case 7:var _1rn=_1q9.c,_1ro=E(_1q9.a),_1rp=function(_1rq,_){return new F(function(){return _1b2(_1ro.b,function(_1rr,_){var _1rs=E(_1q6),_1rt=__app1(E(_1at),_1rs),_1ru=__app3(E(_1q0),_1rs,E(_1rq),E(_1rr)),_1rv=B(_1q1(_1q9.b,_1rs,_)),_1rw=__app1(E(_1aj),_1rs);return new F(function(){return _qV(_);});},_);});},_1rx=E(_1ro.a);switch(_1rx._){case 0:var _1ry=B(_1rp(_1rx.a,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1rn));_1q3=_1qb;return __continue;case 1:var _1rz=B(A1(_1rx.a,_)),_1rA=B(_1rp(_1rz,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1rn));_1q3=_1qb;return __continue;case 2:var _1rB=rMV(E(E(_1rx.a).c)),_1rC=E(_1rB);if(!_1rC._){var _1rD=new T(function(){return B(A1(_1rx.b,new T(function(){return B(_qv(_1rC.a));})));},1),_1rE=B(_1rp(_1rD,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1rn));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1rn));_1q3=_1qb;return __continue;}break;default:var _1rF=rMV(E(E(_1rx.a).c)),_1rG=E(_1rF);if(!_1rG._){var _1rH=B(A2(_1rx.b,E(_1rG.a).a,_)),_1rI=B(_1rp(_1rH,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1rn));_1q3=_1qb;return __continue;}else{var _1qb=_1q6;_1q2=B(_1n8(_1q8,_1rn));_1q3=_1qb;return __continue;}}break;default:var _1rJ=B(_1q1(_1q9.a,_1q6,_)),_1qb=_1q6;_1q2=B(_1n8(_1q8,_1q9.c));_1q3=_1qb;return __continue;}}})(_1q2,_1q3,_));if(_1q4!=__continue){return _1q4;}}},_1rK=function(_1rL){return E(E(_1rL).b);},_1rM=__Z,_1rN=function(_1rO,_1rP,_1rQ,_1rR){var _1rS=E(_1rR);switch(_1rS._){case 0:return new T3(2,_1rP,_1rQ,_1rM);case 1:return new T3(2,_1rP,_1rQ,_1rS.a);default:var _1rT=_1rS.a,_1rU=_1rS.b,_1rV=_1rS.c;return new T1(1,new T(function(){if(!B(A2(_1rO,_1rP,_1rT))){return B(_1rN(_1rO,_1rT,new T3(0,_1rP,_1rQ,_1rU),_1rV));}else{return B(_1rN(_1rO,_1rP,new T3(0,_1rT,_1rU,_1rQ),_1rV));}}));}},_1rW=0,_1rX=function(_1rY,_1rZ,_1s0){return new F(function(){return A1(_1s0,new T2(0,new T2(0,new T(function(){return E(_1rY).b;}),_1rY),_1rZ));});},_1s1=function(_1s2,_1s3,_1s4){var _1s5=function(_1s6){var _1s7=E(_1s6),_1s8=_1s7.b,_1s9=new T(function(){return E(_1s7.a)+E(_1s2)|0;}),_1sa=function(_){var _1sb=nMV(_qe),_1sc=_1sb;return new T(function(){var _1sd=function(_1se){var _1sf=new T(function(){return B(A1(_1s4,new T2(0,_7,E(_1se).b)));});return new T1(0,B(_pi(_1sc,function(_1sg){return E(_1sf);})));},_1sh=new T2(0,_1s9,_1sc),_1si=function(_1sj){var _1sk=new T(function(){var _1sl=E(_1sj),_1sm=E(_1sl.c);if(!_1sm._){var _1sn=E(new T3(1,1,_1sh,E(_1rM)));}else{var _1so=_1sm.a,_1sp=_1sm.c,_1sq=E(_1sm.b),_1sr=E(_1s9),_1ss=E(_1sq.a);if(_1sr>=_1ss){if(_1sr!=_1ss){var _1st=new T3(1,_1so+1|0,_1sq,E(B(_1rN(function(_1su,_1sv){var _1sw=E(E(_1su).a),_1sx=E(E(_1sv).a);return (_1sw>=_1sx)?_1sw==_1sx:true;},_1sh,_1rW,_1sp))));}else{var _1st=new T3(1,_1so+1|0,_1sh,E(B(_1rN(function(_1sy,_1sz){var _1sA=E(E(_1sy).a),_1sB=E(E(_1sz).a);return (_1sA>=_1sB)?_1sA==_1sB:true;},_1sq,_1rW,_1sp))));}var _1sC=_1st;}else{var _1sC=new T3(1,_1so+1|0,_1sh,E(B(_1rN(function(_1sD,_1sE){var _1sF=E(E(_1sD).a),_1sG=E(E(_1sE).a);return (_1sF>=_1sG)?_1sF==_1sG:true;},_1sq,_1rW,_1sp))));}var _1sn=_1sC;}return new T4(0,E(_1sl.a),_1sl.b,E(_1sn),E(_1sl.d));});return function(_1sH,_1sI){return new F(function(){return A1(_1sI,new T2(0,new T2(0,_7,_1sk),_1sH));});};};return B(A(_rS,[_4l,_1s8,_1si,_1s8,_1sd]));});};return new T1(0,_1sa);};return new F(function(){return A(_rS,[_4l,_1s3,_1rX,_1s3,_1s5]);});},_1sJ=function(_1sK,_1sL,_1sM){var _1sN=function(_1sO,_){var _1sP=E(_1sK),_1sQ=__app1(E(_1pU),_1sP.b);return new F(function(){return _1q1(B(_1rK(_1sO)),_1sP.a,_);});},_1sR=function(_1sS){var _1sT=E(_1sS),_1sU=function(_){var _1sV=nMV(new T2(0,_1sT.a,_6));return new T(function(){var _1sW=new T(function(){return B(_rS(_4l,_1sV,_1n3));}),_1sX=function(_1sY){return new F(function(){return _1sZ(E(_1sY).b);});},_1t0=function(_1t1){return new F(function(){return _1s1(_1pV,E(_1t1).b,_1sX);});},_1t2=function(_1t3){var _1t4=E(_1t3);return new F(function(){return A(_1nF,[B(_1rK(_1t4.a)),_1aa,_1n7,_1n7,_1n7,_1aa,_1n7,_1t4.b,_1t0]);});},_1sZ=function(_1t5){return new F(function(){return A2(_1sW,_1t5,_1t2);});},_1t6=function(_1t7){var _1t8=E(_1t7).b,_1t9=function(_){var _1ta=nMV(_1pW);return new T1(1,new T2(1,new T(function(){return B(A1(_1sM,new T2(0,_7,_1t8)));}),new T2(1,new T(function(){return B(_1sZ(_1t8));}),_6)));};return new T1(0,_1t9);};return new T1(0,B(_4t(_1sV,_1sN,_1sT.b,_1t6)));});};return new T1(0,_1sU);};return new F(function(){return _1iF(_1sL,_1sR);});},_1tb="deltaZ",_1tc="deltaY",_1td="deltaX",_1te=new T(function(){return B(unCStr(")"));}),_1tf=new T(function(){return B(_fi(0,2,_1te));}),_1tg=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_1tf));}),_1th=function(_1ti){return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",new T(function(){return B(_fi(0,_1ti,_1tg));}))));});},_1tj=function(_1tk,_){return new T(function(){var _1tl=Number(E(_1tk)),_1tm=jsTrunc(_1tl);if(_1tm<0){return B(_1th(_1tm));}else{if(_1tm>2){return B(_1th(_1tm));}else{return _1tm;}}});},_1tn=0,_1to=new T3(0,_1tn,_1tn,_1tn),_1tp="button",_1tq=new T(function(){return eval("jsGetMouseCoords");}),_1tr=function(_1ts,_){var _1tt=E(_1ts);if(!_1tt._){return _6;}else{var _1tu=B(_1tr(_1tt.b,_));return new T2(1,new T(function(){var _1tv=Number(E(_1tt.a));return jsTrunc(_1tv);}),_1tu);}},_1tw=function(_1tx,_){var _1ty=__arr2lst(0,_1tx);return new F(function(){return _1tr(_1ty,_);});},_1tz=function(_1tA,_){return new F(function(){return _1tw(E(_1tA),_);});},_1tB=function(_1tC,_){return new T(function(){var _1tD=Number(E(_1tC));return jsTrunc(_1tD);});},_1tE=new T2(0,_1tB,_1tz),_1tF=function(_1tG,_){var _1tH=E(_1tG);if(!_1tH._){return _6;}else{var _1tI=B(_1tF(_1tH.b,_));return new T2(1,_1tH.a,_1tI);}},_1tJ=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_1tK=new T6(0,_2o,_2p,_6,_1tJ,_2o,_2o),_1tL=new T(function(){return B(_1R(_1tK));}),_1tM=function(_){return new F(function(){return die(_1tL);});},_1tN=function(_1tO){return E(E(_1tO).a);},_1tP=function(_1tQ,_1tR,_1tS,_){var _1tT=__arr2lst(0,_1tS),_1tU=B(_1tF(_1tT,_)),_1tV=E(_1tU);if(!_1tV._){return new F(function(){return _1tM(_);});}else{var _1tW=E(_1tV.b);if(!_1tW._){return new F(function(){return _1tM(_);});}else{if(!E(_1tW.b)._){var _1tX=B(A3(_1tN,_1tQ,_1tV.a,_)),_1tY=B(A3(_1tN,_1tR,_1tW.a,_));return new T2(0,_1tX,_1tY);}else{return new F(function(){return _1tM(_);});}}}},_1tZ=function(_1u0,_1u1,_){if(E(_1u0)==7){var _1u2=__app1(E(_1tq),_1u1),_1u3=B(_1tP(_1tE,_1tE,_1u2,_)),_1u4=__get(_1u1,E(_1td)),_1u5=__get(_1u1,E(_1tc)),_1u6=__get(_1u1,E(_1tb));return new T(function(){return new T3(0,E(_1u3),E(_2o),E(new T3(0,_1u4,_1u5,_1u6)));});}else{var _1u7=__app1(E(_1tq),_1u1),_1u8=B(_1tP(_1tE,_1tE,_1u7,_)),_1u9=__get(_1u1,E(_1tp)),_1ua=__eq(_1u9,E(_4r));if(!E(_1ua)){var _1ub=B(_1tj(_1u9,_));return new T(function(){return new T3(0,E(_1u8),E(new T1(1,_1ub)),E(_1to));});}else{return new T(function(){return new T3(0,E(_1u8),E(_2o),E(_1to));});}}},_1uc=function(_1ud,_1ue,_){return new F(function(){return _1tZ(_1ud,E(_1ue),_);});},_1uf="mouseout",_1ug="mouseover",_1uh="mousemove",_1ui="mouseup",_1uj="mousedown",_1uk="dblclick",_1ul="click",_1um="wheel",_1un=function(_1uo){switch(E(_1uo)){case 0:return E(_1ul);case 1:return E(_1uk);case 2:return E(_1uj);case 3:return E(_1ui);case 4:return E(_1uh);case 5:return E(_1ug);case 6:return E(_1uf);default:return E(_1um);}},_1up=new T2(0,_1un,_1uc),_1uq=function(_1ur,_){return new T1(1,_1ur);},_1us=new T2(0,_2E,_1uq),_1ut=function(_1uu,_1uv,_1uw){var _1ux=function(_1uy,_){return new F(function(){return _e(new T(function(){return B(A3(_1uu,_1uy,_1uv,_2H));}),_6,_);});};return new F(function(){return A1(_1uw,new T2(0,_1ux,_1uv));});},_1uz=new T2(0,_4f,_1ni),_1uA=new T2(0,_1uz,_1ut),_1uB=function(_1uC,_1uD,_1uE){return new F(function(){return A1(_1uE,new T2(0,new T2(0,new T(function(){return E(E(_1uC).a);}),_1uC),_1uD));});},_1uF=16,_1uG=function(_1uH,_1uI,_1uJ){var _1uK=E(_1uH);if(!_1uK._){return new F(function(){return A1(_1uJ,new T2(0,_6,_1uI));});}else{var _1uL=function(_1uM){var _1uN=E(_1uM);return new F(function(){return _1uG(_1uK.b,_1uN.b,function(_1uO){var _1uP=E(_1uO);return new F(function(){return A1(_1uJ,new T2(0,new T2(1,_1uN.a,_1uP.a),_1uP.b));});});});};return new F(function(){return A2(E(_1uK.a).a,_1uI,_1uL);});}},_1uQ=function(_1uR,_1uS,_1uT){var _1uU=E(_1uR);if(!_1uU._){return new F(function(){return A1(_1uT,new T2(0,_6,_1uS));});}else{var _1uV=E(_1uU.a),_1uW=function(_1uX){var _1uY=E(_1uX),_1uZ=function(_1v0){var _1v1=E(_1v0),_1v2=_1v1.a;return new F(function(){return A1(_1uT,new T2(0,new T(function(){if(!E(_1uY.a)){return E(_1v2);}else{return new T2(1,_1uV,_1v2);}}),_1v1.b));});};return new F(function(){return _1uQ(_1uU.b,_1uY.b,_1uZ);});};return new F(function(){return A2(_1uV.b,_1uS,_1uW);});}},_1v3=function(_1v4,_1v5){var _1v6=E(_1v5);switch(_1v6._){case 0:return __Z;case 1:var _1v7=B(_1v3(_1v4,_1v6.a));if(!_1v7._){return __Z;}else{var _1v8=E(_1v7.b);return new T3(1,_1v7.a,_1v8.c,new T3(2,_1v8.a,_1v8.b,_1v7.c));}break;default:var _1v9=_1v6.a,_1va=_1v6.b,_1vb=_1v6.c,_1vc=B(_1v3(_1v4,_1vb));if(!_1vc._){return new T3(1,_1v9,_1va,new T1(1,_1vb));}else{var _1vd=_1vc.a,_1ve=_1vc.c;if(!B(A2(_1v4,_1v9,_1vd))){var _1vf=E(_1vc.b),_1vg=_1vf.a,_1vh=_1vf.b;return new T3(1,_1vd,_1vf.c,new T1(1,new T(function(){if(!B(A2(_1v4,_1v9,_1vg))){return B(_1rN(_1v4,_1vg,new T3(0,_1v9,_1va,_1vh),_1ve));}else{return B(_1rN(_1v4,_1v9,new T3(0,_1vg,_1vh,_1va),_1ve));}})));}else{return new T3(1,_1v9,_1va,new T1(1,_1vb));}}}},_1vi=function(_1vj){var _1vk=new T(function(){var _1vl=E(_1vj),_1vm=E(_1vl.c);if(!_1vm._){var _1vn=__Z;}else{var _1vo=B(_1v3(function(_1vp,_1vq){var _1vr=E(E(_1vp).a),_1vs=E(E(_1vq).a);return (_1vr>=_1vs)?_1vr==_1vs:true;},_1vm.c));if(!_1vo._){var _1vt=__Z;}else{var _1vt=new T3(1,_1vm.a-1|0,_1vo.a,E(_1vo.c));}var _1vn=_1vt;}return new T4(0,E(_1vl.a),_1vl.b,E(_1vn),E(_1vl.d));});return function(_1vu,_1vv){return new F(function(){return A1(_1vv,new T2(0,new T2(0,_7,_1vk),_1vu));});};},_1vw=function(_1vx,_1vy,_1vz){return new F(function(){return A1(_1vz,new T2(0,new T2(0,new T(function(){var _1vA=E(E(_1vx).c);if(!_1vA._){return __Z;}else{return new T1(1,_1vA.b);}}),_1vx),_1vy));});},_1vB=function(_1vC,_1vD,_1vE){return new F(function(){return A1(_1vE,new T2(0,new T2(0,_7,new T(function(){var _1vF=E(_1vC);return new T4(0,E(_1vF.a),_1vF.b+1|0,E(_1vF.c),E(_1vF.d));})),_1vD));});},_1vG=function(_1vH,_1vI){return new T1(0,B(_1vJ(_1vH)));},_1vK=function(_1vL){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_1vL));}))));});},_1vM=new T(function(){return B(_1vK("w_sPPq ((), MVar WorldState) -> Action"));}),_1vN=function(_1vO){return new F(function(){return _1vG(E(_1vO).b,_1vM);});},_1vP=function(_1vQ){var _1vR=E(_1vQ).b;return new F(function(){return A(_rS,[_4l,_1vR,_1vB,_1vR,_1vN]);});},_1vS=function(_1vT,_1vU){var _1vV=new T(function(){return B(A2(_b1,_1vT,_7));}),_1vW=new T(function(){return B(_1vS(_1vT,_1vU));});return new F(function(){return A3(_ap,_1vT,_1vU,function(_1vX){return (!E(_1vX))?E(_1vV):E(_1vW);});});},_1vY=function(_1vZ){var _1w0=E(_1vZ),_1w1=function(_1w2,_1w3){var _1w4=function(_1w5){return new F(function(){return A1(_1w3,new T2(0,_cm,E(_1w5).b));});},_1w6=function(_1w7){var _1w8=E(_1w7),_1w9=_1w8.b,_1wa=E(_1w8.a);if(!_1wa._){return new F(function(){return A1(_1w3,new T2(0,_5i,_1w9));});}else{var _1wb=E(_1wa.a);if(E(_1wb.a)<=E(_1w0.a)){var _1wc=new T(function(){return B(A(_rS,[_4l,_1w9,_1vi,_1w9,_1w4]));});return new T1(0,B(_p6(_1wb.b,_7,function(_1wd){return E(_1wc);})));}else{return new F(function(){return A1(_1w3,new T2(0,_5i,_1w9));});}}};return new F(function(){return A(_rS,[_4l,_1w2,_1vw,_1w2,_1w6]);});};return new F(function(){return A(_1vS,[_4f,_1w1,_1w0.b,_1vP]);});},_1we=function(_1wf){var _1wg=E(_1wf).b;return new F(function(){return A(_rS,[_4l,_1wg,_1rX,_1wg,_1vY]);});},_1wh=function(_1wi){var _1wj=E(_1wi),_1wk=_1wj.b,_1wl=function(_1wm,_1wn,_1wo){return new F(function(){return A1(_1wo,new T2(0,new T2(0,_7,new T(function(){var _1wp=E(_1wm);return new T4(0,E(_1wj.a),_1wp.b,E(_1wp.c),E(_1wp.d));})),_1wn));});};return new F(function(){return A(_rS,[_4l,_1wk,_1wl,_1wk,_1we]);});},_1wq=function(_1wr){var _1ws=E(_1wr),_1wt=_1ws.a;return new F(function(){return _1uG(_1wt,_1ws.b,function(_1wu){return new F(function(){return _1uQ(_1wt,E(_1wu).b,_1wh);});});});},_1vJ=function(_1wv){var _1ww=new T(function(){return B(A(_rS,[_4l,_1wv,_1uB,_1wv,_1wq]));});return new F(function(){return _q5(_1uF,function(_1wx){return E(_1ww);});});},_1wy=2,_1wz=4,_1wA=3,_1wB=function(_1wC,_1wD,_1wE){return new F(function(){return A1(_1wE,new T2(0,new T2(0,new T(function(){return E(E(E(_1wC).d).b);}),_1wC),_1wD));});},_1wF=new T(function(){return eval("document");}),_1wG=new T1(0,_5i),_1wH=new T1(0,_cm),_1wI=new T1(1,_6),_1wJ=__Z,_1wK=new T0(2),_1wL=new T2(0,_qd,_1wK),_1wM=new T4(0,E(_6),0,E(_1wJ),E(_1wL)),_1wN=new T2(0,_1wM,_6),_1wO=function(_1wP){return E(E(_1wP).a);},_1wQ=function(_1wR){return E(E(_1wR).b);},_1wS=function(_1wT){return E(E(_1wT).a);},_1wU=function(_){return new F(function(){return nMV(_2o);});},_1wV=new T(function(){return B(_4n(_1wU));}),_1wW=new T(function(){return eval("(function(e,name,f){e.addEventListener(name,f,false);return [f];})");}),_1wX=function(_1wY,_1wZ,_1x0,_1x1,_1x2,_1x3){var _1x4=B(_pw(_1wY)),_1x5=B(_py(_1x4)),_1x6=new T(function(){return B(_pC(_1x4));}),_1x7=new T(function(){return B(_b1(_1x5));}),_1x8=new T(function(){return B(A2(_1wO,_1wZ,_1x1));}),_1x9=new T(function(){return B(A2(_1wS,_1x0,_1x2));}),_1xa=function(_1xb){return new F(function(){return A1(_1x7,new T3(0,_1x9,_1x8,_1xb));});},_1xc=function(_1xd){var _1xe=new T(function(){var _1xf=new T(function(){var _1xg=__createJSFunc(2,function(_1xh,_){var _1xi=B(A2(E(_1xd),_1xh,_));return _4r;}),_1xj=_1xg;return function(_){return new F(function(){return __app3(E(_1wW),E(_1x8),E(_1x9),_1xj);});};});return B(A1(_1x6,_1xf));});return new F(function(){return A3(_ap,_1x5,_1xe,_1xa);});},_1xk=new T(function(){var _1xl=new T(function(){return B(_pC(_1x4));}),_1xm=function(_1xn){var _1xo=new T(function(){return B(A1(_1xl,function(_){var _=wMV(E(_1wV),new T1(1,_1xn));return new F(function(){return A(_1wQ,[_1x0,_1x2,_1xn,_]);});}));});return new F(function(){return A3(_ap,_1x5,_1xo,_1x3);});};return B(A2(_pE,_1wY,_1xm));});return new F(function(){return A3(_ap,_1x5,_1xk,_1xc);});},_1xp=function(_1xq,_1xr){return new F(function(){return A1(_1xr,new T2(0,_7,_1xq));});},_1xs=function(_1xt,_1xu){return function(_){var _1xv=nMV(_1wN),_1xw=_1xv,_1xx=function(_1xy){return new F(function(){return A1(_1xu,E(_1xy).a);});},_1xz=function(_1xA){return new F(function(){return A2(_1xt,E(_1xA).b,_1xx);});},_1xB=function(_){var _1xC=nMV(_1wI),_1xD=_1xC,_1xE=new T(function(){var _1xF=function(_1xG){return new F(function(){return _1xH(E(_1xG).b);});},_1xH=function(_1xI){var _1xJ=function(_1xK){var _1xL=function(_1xM){var _1xN=E(_1xM),_1xO=_1xN.b,_1xP=E(_1xK),_1xQ=function(_1xR,_1xS,_1xT){var _1xU=function(_1xV,_1xW){while(1){var _1xX=B((function(_1xY,_1xZ){var _1y0=E(_1xZ);switch(_1y0._){case 0:_1xV=new T(function(){return B(_1xU(_1xY,_1y0.d));});_1xW=_1y0.c;return __continue;case 1:var _1y1=new T(function(){return B(_1de(_4l,_1y0.b,_1xR));}),_1y2=function(_1y3){var _1y4=new T(function(){return B(A1(_1y1,_1y3));}),_1y5=function(_1y6){return new F(function(){return A1(_1y4,function(_1y7){return new F(function(){return A2(_1xY,E(_1y7).b,_1y6);});});});};return E(_1y5);};return E(_1y2);default:return E(_1xY);}})(_1xV,_1xW));if(_1xX!=__continue){return _1xX;}}},_1y8=E(_1xN.a);if(!_1y8._){var _1y9=_1y8.c,_1ya=_1y8.d;if(_1y8.b>=0){return new F(function(){return A(_1xU,[new T(function(){return B(_1xU(_1xp,_1ya));}),_1y9,_1xS,_1xT]);});}else{return new F(function(){return A(_1xU,[new T(function(){return B(_1xU(_1xp,_1y9));}),_1ya,_1xS,_1xT]);});}}else{return new F(function(){return A(_1xU,[_1xp,_1y8,_1xS,_1xT]);});}};switch(E(_1xP.a)){case 2:return new F(function(){return _1xQ(_1wH,_1xO,_1xF);});break;case 3:return new F(function(){return _1xQ(_1wG,_1xO,_1xF);});break;case 4:var _1yb=new T(function(){return E(E(_1xP.b).a);});return new F(function(){return _1xQ(new T1(1,new T2(0,new T(function(){return E(E(_1yb).a);}),new T(function(){return E(E(_1yb).b);}))),_1xO,_1xF);});break;default:return new F(function(){return _1xH(_1xO);});}};return new F(function(){return A(_rS,[_4l,_1xI,_1wB,_1xI,_1xL]);});};return new T1(0,B(_pi(_1xD,_1xJ)));};return B(_1xH(_1xw));}),_1yc=new T(function(){var _1yd=new T(function(){return B(_1wX(_1uA,_1us,_1up,_1wF,_1wz,function(_1ye){return new F(function(){return _1de(_4l,_1xD,new T2(0,_1wz,_1ye));});}));}),_1yf=new T(function(){return B(_1wX(_1uA,_1us,_1up,_1wF,_1wA,function(_1yg){return new F(function(){return _1de(_4l,_1xD,new T2(0,_1wA,_1yg));});}));}),_1yh=function(_1yi){return new F(function(){return A2(_1yf,E(_1yi).b,_1xz);});};return B(A(_1wX,[_1uA,_1us,_1up,_1wF,_1wy,function(_1yj){return new F(function(){return _1de(_4l,_1xD,new T2(0,_1wy,_1yj));});},_1xw,function(_1yk){return new F(function(){return A2(_1yd,E(_1yk).b,_1yh);});}]));});return new T1(1,new T2(1,_1yc,new T2(1,_1xE,_6)));};return new T1(1,new T2(1,new T1(0,_1xB),new T2(1,new T(function(){return new T1(0,B(_1vJ(_1xw)));}),_6)));};},_1yl=new T(function(){return eval("(function(id){return document.getElementById(id);})");}),_1ym=function(_1yn,_1yo){var _1yp=function(_){var _1yq=__app1(E(_1yl),E(_1yo)),_1yr=__eq(_1yq,E(_4r));return (E(_1yr)==0)?new T1(1,_1yq):_2o;};return new F(function(){return A2(_pC,_1yn,_1yp);});},_1ys=new T(function(){return B(unCStr("Canvas not found!"));}),_1yt=new T(function(){return B(err(_1ys));}),_1yu="canvas",_1yv=new T(function(){return eval("(Util.onload)");}),_1yw=function(_){var _1yx=__app1(E(_1yv),E(_4r)),_1yy=B(A3(_1ym,_2G,_1yu,_)),_1yz=E(_1yy);if(!_1yz._){return E(_1yt);}else{var _1yA=E(_1yz.a),_1yB=__app1(E(_1),_1yA);if(!_1yB){return E(_1yt);}else{var _1yC=__app1(E(_0),_1yA),_1yD=_1yC,_1yE=new T(function(){return new T1(0,B(_1xs(function(_1yF,_1yG){return new T1(0,B(_1sJ(new T2(0,_1yD,_1yA),_1yF,_1yG)));},_p4)));});return new F(function(){return _e(_1yE,_6,_);});}}},_1yH=function(_){return new F(function(){return _1yw(_);});};
var hasteMain = function() {B(A(_1yH, [0]));};window.onload = hasteMain;