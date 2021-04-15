'use-strict';
"use strict";
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : new P(function (resolve) { resolve(result.value); }).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var __generator = (this && this.__generator) || function (thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
    return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (_) try {
            if (f = 1, y && (t = y[op[0] & 2 ? "return" : op[0] ? "throw" : "next"]) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [0, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
};
var _this = this;
exports.__esModule = true;
var util = require('util');
var spawn = require('child_process').spawn;
var mutex_1 = require("./mutex");
var fs_1 = require("fs");
var exec_glob = util.promisify(require('child_process').exec);
var WORKDIR = "_____WORKDIR";
var BASE_ASSERT_DEF_UA = "int assert(int a) { if(a == 0){__VERIFIER_error();}\n ";
var BASE_ASSERT_DEF_CBMC = "int assert(int a) { __CPROVER_ASSERT(\"postcondition\", a);}\n ";
var BASE_ASSUME_DEF_UA = "int assume(int a) { if(a == 0){exit();}\n ";
var BASE_ASSUME_DEF_CBMC = "int assume(int a) {__CPROVER_assume(a);}\n ";
var exec_wd = function (cmd) { return exec_glob("cd " + WORKDIR + " && " + cmd); };
var createWorkdir = function () { return __awaiter(_this, void 0, void 0, function () { return __generator(this, function (_a) {
    switch (_a.label) {
        case 0: return [4 /*yield*/, exec_glob("mkdir " + WORKDIR)];
        case 1: return [2 /*return*/, _a.sent()];
    }
}); }); };
var cleanUp = function () { return __awaiter(_this, void 0, void 0, function () {
    var _a;
    return __generator(this, function (_b) {
        switch (_b.label) {
            case 0:
                _b.trys.push([0, 2, , 3]);
                return [4 /*yield*/, exec_glob("rm -rf " + WORKDIR)];
            case 1:
                _b.sent();
                return [3 /*break*/, 3];
            case 2:
                _a = _b.sent();
                return [3 /*break*/, 3];
            case 3: return [2 /*return*/];
        }
    });
}); };
var addDefsToFile = function (file, verifier) { return __awaiter(_this, void 0, void 0, function () {
    return __generator(this, function (_a) {
        fs_1.writeFileSync(WORKDIR + "/" + file, fs_1.readFileSync(WORKDIR + "/" + file).toString());
        if (verifier === "ua") {
            fs_1.writeFileSync(WORKDIR + "/" + file, BASE_ASSERT_DEF_UA + BASE_ASSUME_DEF_UA + fs_1.readFileSync(WORKDIR + "/" + file).toString());
        }
        else {
            fs_1.writeFileSync(WORKDIR + "/" + file, BASE_ASSERT_DEF_CBMC + BASE_ASSUME_DEF_CBMC + fs_1.readFileSync(WORKDIR + "/" + file).toString());
        }
        return [2 /*return*/];
    });
}); };
var ProofStatus;
(function (ProofStatus) {
    ProofStatus[ProofStatus["success"] = 0] = "success";
    ProofStatus[ProofStatus["fail"] = 1] = "fail";
    ProofStatus[ProofStatus["unattempted"] = 2] = "unattempted";
})(ProofStatus || (ProofStatus = {}));
function waitForEventWithTimeout(socket, event, t) {
    return new Promise(function (resolve, reject) {
        var timer;
        function listener(data) {
            clearTimeout(timer);
            socket.removeListener(event, listener);
            resolve("" + data);
        }
        socket.on(event, listener);
        timer = setTimeout(function () {
            socket.removeListener(event, listener);
            reject(new Error("timeout"));
        }, t);
    });
}
var verify = function (filename, verifier, sync) { return __awaiter(_this, void 0, void 0, function () {
    var _this = this;
    function runCommand(command) {
        return __awaiter(this, void 0, void 0, function () {
            var chunk, out;
            return __generator(this, function (_a) {
                switch (_a.label) {
                    case 0:
                        child.stdin.write(command + '\n');
                        _a.label = 1;
                    case 1:
                        if (!true) return [3 /*break*/, 3];
                        return [4 /*yield*/, waitForEventWithTimeout(child.stdout, 'data', 5000)];
                    case 2:
                        chunk = _a.sent();
                        buffer += chunk;
                        if (buffer.includes("$SICC_SERVER_DONE")) {
                            out = buffer.split("$SICC_SERVER_DONE");
                            buffer = out.slice(1).join("");
                            return [2 /*return*/, out[0]];
                        }
                        return [3 /*break*/, 1];
                    case 3: return [2 /*return*/];
                }
            });
        });
    }
    function getNode(fun) {
        if (status[fun]) {
            return status[fun];
        }
        else {
            status[fun] = {
                "function": fun,
                proofLocal: ProofStatus.unattempted,
                proofActual: ProofStatus.unattempted,
                mutex: new mutex_1["default"](),
                provenParent: null
            };
            return status[fun];
        }
    }
    function getParents(fun) {
        return __awaiter(this, void 0, void 0, function () {
            var response;
            return __generator(this, function (_a) {
                switch (_a.label) {
                    case 0: return [4 /*yield*/, runCommand("parents " + fun)];
                    case 1:
                        response = _a.sent();
                        return [2 /*return*/, response.split("\n").map(function (s) { return s.trim(); }).filter(function (s) { return s != ""; })];
                }
            });
        });
    }
    var buffer, child, status, assertFuns, prove, _i, assertFuns_1, fun;
    return __generator(this, function (_a) {
        switch (_a.label) {
            case 0:
                buffer = "";
                child = spawn("./src/_build/default/main.exe", [filename]);
                child.stdin.setEncoding('utf-8');
                console.log(filename);
                status = {};
                return [4 /*yield*/, getParents("assert")];
            case 1:
                assertFuns = _a.sent();
                prove = function (fun, previous) { return __awaiter(_this, void 0, void 0, function () {
                    var _a, targetfile, code, pwd, ua, e_1, parents;
                    return __generator(this, function (_b) {
                        switch (_b.label) {
                            case 0: return [4 /*yield*/, fun.mutex.lock()];
                            case 1:
                                _b.sent();
                                _a = fun.proofActual;
                                switch (_a) {
                                    case ProofStatus.unattempted: return [3 /*break*/, 2];
                                    case ProofStatus.success: return [3 /*break*/, 15];
                                    case ProofStatus.fail: return [3 /*break*/, 15];
                                }
                                return [3 /*break*/, 16];
                            case 2:
                                _b.trys.push([2, 10, , 15]);
                                targetfile = fun["function"] + ".c";
                                return [4 /*yield*/, runCommand("print " + fun["function"])];
                            case 3:
                                code = _b.sent();
                                fs_1.writeFileSync(WORKDIR + "/" + targetfile, code);
                                addDefsToFile(targetfile, verifier);
                                console.log(fun["function"]);
                                if (!(verifier == "cbmc")) return [3 /*break*/, 5];
                                return [4 /*yield*/, exec_wd("cbmc " + targetfile + " --unwinding-assertions --unwind 201 --function " + fun["function"] + " > /dev/null")];
                            case 4:
                                _b.sent();
                                return [3 /*break*/, 9];
                            case 5:
                                if (!(verifier == "ua")) return [3 /*break*/, 9];
                                return [4 /*yield*/, exec_wd("pwd")
                                        .then(function (r) { return r.stdout.trim(); })["catch"](function (err) { return console.log(err); })];
                            case 6:
                                pwd = _b.sent();
                                return [4 /*yield*/, exec_wd("mkdir " + fun["function"])];
                            case 7:
                                _b.sent();
                                fs_1.writeFileSync(pwd + "/" + fun["function"] + "/PropertyUnreachCall.prp", "CHECK( init(" + fun["function"] + "()), LTL(G ! call(__VERIFIER_error())) )");
                                return [4 /*yield*/, exec_glob("cd ~/uauto && ./Ultimate.py --spec " + pwd + "/" + fun["function"] + "/PropertyUnreachCall.prp --architecture 64bit --file " + pwd + "/" + targetfile + " | grep -E -- 'TRUE|FALSE'")];
                            case 8:
                                ua = _b.sent();
                                console.log(fun["function"] + ua.stdout);
                                if (!ua.stdout.includes("TRUE")) {
                                    throw Error;
                                }
                                _b.label = 9;
                            case 9:
                                fun.proofActual = ProofStatus.success;
                                fun.proofLocal = ProofStatus.success;
                                fun.provenParent = fun;
                                return [3 /*break*/, 15];
                            case 10:
                                e_1 = _b.sent();
                                fun.proofLocal = ProofStatus.fail;
                                return [4 /*yield*/, getParents(fun["function"])];
                            case 11:
                                parents = _b.sent();
                                if (!(parents.length > 0)) return [3 /*break*/, 13];
                                return [4 /*yield*/, Promise.all(parents.map(function (p) { return prove(getNode(p), fun); }))];
                            case 12:
                                _b.sent();
                                return [3 /*break*/, 14];
                            case 13:
                                fun.proofLocal = ProofStatus.fail;
                                _b.label = 14;
                            case 14: return [3 /*break*/, 15];
                            case 15:
                                {
                                    if (previous) {
                                        previous.provenParent = fun.provenParent;
                                        previous.proofActual = fun.proofActual;
                                    }
                                }
                                _b.label = 16;
                            case 16:
                                fun.mutex.release();
                                return [2 /*return*/];
                        }
                    });
                }); };
                if (!sync) return [3 /*break*/, 6];
                _i = 0, assertFuns_1 = assertFuns;
                _a.label = 2;
            case 2:
                if (!(_i < assertFuns_1.length)) return [3 /*break*/, 5];
                fun = assertFuns_1[_i];
                return [4 /*yield*/, prove(getNode(fun), null)];
            case 3:
                _a.sent();
                _a.label = 4;
            case 4:
                _i++;
                return [3 /*break*/, 2];
            case 5: return [3 /*break*/, 8];
            case 6: return [4 /*yield*/, Promise.all(assertFuns.map(function (fun) { return prove(getNode(fun), null); }))];
            case 7:
                _a.sent();
                _a.label = 8;
            case 8: return [2 /*return*/, assertFuns.map(function (fun) {
                    var getLOC = function (fun) {
                        return fun;
                    };
                    return {
                        loc: getLOC(fun),
                        isTrue: status[fun].proofActual === ProofStatus.success,
                        provedAt: status[fun].provenParent ? getLOC(status[fun].provenParent["function"]) : null
                    };
                })];
        }
    });
}); };
module.exports = {
    createWorkdir: createWorkdir,
    cleanUp: cleanUp,
    verify: verify
};
