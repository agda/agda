// TODO
// Some of the primitives here are curried, some not. We probably should make this more consistent,
// or maybe just introduce a clear naming convention.

var biginteger = require("biginteger")

// Integers

exports.primIntegerFromString = function(x) {
  return biginteger.BigInteger(x);
};
exports.primShowInteger = function(x) {
  return x.toString();
};

exports.primIntegerPlus = function(x,y) {
  return x.add(y);
};
exports.primIntegerMinus = function(x,y) {
  return x.subtract(y);
};
exports.primIntegerMultiply = function(x,y) {
  return x.multiply(y);
};
exports.primIntegerEqual = function(x,y) {
  return x.compare(y) == 0;
};
exports.primIntegerGreaterOrEqualThan = function(x,y) {
  return x.compare(y) >= 0;
};
exports.primIntegerLessThan = function(x,y) {
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
    return x==y;
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
  return sqrt(x);
};

// As Javascript is strict, this should be fine in general. Not sure
// what PSeq (Axiom ...) (...) should do?
exports.primSeq = function(x, y) {
  return y;
};
