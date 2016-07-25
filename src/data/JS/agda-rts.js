
var biginteger = require("biginteger")

exports.primIntegerFromString = function(x) {
  return biginteger.BigInteger(x);
};
exports.primShowInteger = function(x) {
  return x.toString();
};

exports.primIntegerAdd = function(x,y) {
  return x.add(y);
};
exports.primIntegerSubtract = function(x,y) {
  return x.subtract(y);
};
exports.primIntegerMultiply = function(x,y) {
  return x.multiply(y);
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
}
