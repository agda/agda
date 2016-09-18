// NOTE:
// Some of the primitives here are curried, some are not. All uncurried primitives are prefixed by 'u'.

var biginteger = require("biginteger")

// Integers

exports.primIntegerFromString = function(x) {
  return biginteger.BigInteger(x);
};
exports.primShowInteger = function(x) {
  return x.toString();
};

exports.uprimIntegerPlus = function(x,y) {
  return x.add(y);
};
exports.uprimIntegerMinus = function(x,y) {
  return x.subtract(y);
};
exports.uprimIntegerMultiply = function(x,y) {
  return x.multiply(y);
};
exports.uprimIntegerEqual = function(x,y) {
  return x.compare(y) == 0;
};
exports.uprimIntegerGreaterOrEqualThan = function(x,y) {
  return x.compare(y) >= 0;
};
exports.uprimIntegerLessThan = function(x,y) {
  return x.compare(y) == -1;
};

exports.primNatMinus = function(x) {
  return function(y) {
    var z = x.subtract(y);
    if (z.isNegative()) {
      return biginteger.ZERO;
    } else {
      return z;
    }
  };
};

// Floats

exports.primShowFloat = function(x) {
  return x.toString();
};
exports.primFloatEquality = function(x) {
  return function(y) {
    return Object.is(x,y);
  };
};
exports.primFloatLess = function(x) {
  return function(y) {
    return x<y;
  };
};
exports.primFloatPlus = function(x) {
  return function(y) {
    return x+y;
  };
};
exports.primFloatMinus = function(x) {
  return function(y) {
    return x-y;
  };
};
exports.primFloatTimes = function(x) {
  return function(y) {
    return x*y;
  };
};
exports.primFloatDiv = function(x) {
  return function(y) {
    return x/y;
  };
};
exports.primFloatSqrt = function(x) {
  return Math.sqrt(x);
};

exports.primSin = function(x) {
  return Math.sin(x);
};

exports.primExp = function(x) {
  return Math.exp(x);
};

// As Javascript is strict, this should be fine in general. Not sure
// what PSeq (Axiom ...) (...) should do?
exports.primSeq = function(x, y) {
  return y;
};
