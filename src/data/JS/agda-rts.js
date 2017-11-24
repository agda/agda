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
exports.uprimIntegerRem = function(x, y) {
  return x.remainder(y);
};
exports.uprimIntegerQuot = function(x, y) {
  return x.quotient(y);
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
  // See Issue #2192.
  if (Number.isInteger(x)) {
    if (Object.is(x,-0.0)) {
      return ("-0.0");
    } else {
        var a = x.toString();
        return (a + ".0");
    }
  } else {
    return x.toString();
  }
};

exports.primFloatEquality = function(x) {
  return function(y) {
    return Object.is(x,y);
  };
};

exports.primFloatNumericalEquality = function(x) {
  return function(y) {
    return x==y;
  };
};

exports.primFloatNumericalLess = function(x) {
  return function(y) {
    return x < y;
  };
};

exports.uprimFloatEquality = function(x, y) {
  return Object.is(x,y);
};

exports.primFloatLess = function(x) {
  return function(y) {
    if(x == Number.NEGATIVE_INFINITY) {
      return y != Number.NEGATIVE_INFINITY;
    } else if(y == Number.NEGATIVE_INFINITY) {
      return false;
    } else if(isNaN(x)) {
      return !isNaN(y);
    } else if(isNaN(y)) {
      return false;
    } else {
      return x < y || Object.is(x, -0.0) && Object.is(y, 0.0);
    }
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

exports.primFloatNegate = function(x) {
  return -x;
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

exports.primCos = function(x) {
  return Math.cos(x);
};

exports.primTan = function(x) {
  return Math.tan(x);
};

exports.primASin = function(x) {
  return Math.asin(x);
};

exports.primACos = function(x) {
  return Math.acos(x);
};

exports.primATan = function(x) {
  return Math.atan(x);
};

exports.primATan2 = function(y) {
  return function(x){
    return Math.atan2(y,x);
  }
};

exports.primExp = function(x) {
  return Math.exp(x);
};

// As Javascript is strict, this should be fine in general. Not sure
// what PSeq (Axiom ...) (...) should do?
exports.primSeq = function(x, y) {
  return y;
};

exports.primShowQName = function(x) {
  return x["name"];
};
exports.uprimQNameEquality = function(x,y) {
  return x["id"].compare(y["id"]) == 0 && x["moduleId"].compare(y["moduleId"]) == 0;
};
exports.primQNameEquality = function(x) {
  return function(y) {
    return exports.uprimQNameEquality(x, y);
  };
};
exports.primQNameLess = function(x) {
  return function(y) {
    switch (x["id"].compare(y["id"])) {
      case -1: return true;
      case 1:  return false;
      case 0:
        return x["moduleId"].compare(y["moduleId"]) == -1;
    }
  };
};
exports.primQNameFixity = function(x) {
  return x["fixity"];
};

// Words
var twoTo64 = exports.primIntegerFromString("18446744073709551616");

exports.primWord64ToNat = function(x) { return x; };
exports.primWord64FromNat = function(x) { return x.remainder(twoTo64); };

exports.uprimWord64Plus = function(x,y) {
  return x.add(y).remainder(twoTo64);
};
exports.uprimWord64Minus = function(x,y) {
  return x.add(twoTo64).subtract(y).remainder(twoTo64);
};
exports.uprimWord64Multiply = function(x,y) {
  return x.multiply(y).remainder(twoTo64);
};
