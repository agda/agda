var modules = {};
var require = function (moduleName) {
    if (modules[moduleName] == undefined) {
	var module = {};
	var exports = {};
	eval (readFile (moduleName.replace(/\./g, "/") + ".js"));
	modules[moduleName] = exports;
    }
    return modules[moduleName];
};
var module = {};
var exports = {};
var visitor = {
    "ε": function () {},
    "_,_": function (ts,us) { ts(visitor); us(visitor); },
    "assert": function (b,ok,msg) { 
	if (b) {
 	    print("OK " + msg);
	} else {
	    print("FAIL " + msg); 
	    java.lang.System.exit(1); 
	}
    }
};
eval(readFile(arguments[0]));
print ("-- " + module.id + " --");
exports.tests()(visitor);
