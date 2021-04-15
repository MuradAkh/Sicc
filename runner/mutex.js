"use strict";
// Thanks to
// https://stackoverflow.com/questions/48563969/c-like-mutex-in-nodejs
exports.__esModule = true;
var Mutex = /** @class */ (function () {
    function Mutex() {
        var _this = this;
        this.lock = function () {
            return new Promise(function (resolve, reject) {
                if (_this.locked) {
                    _this.queue.push({ resolve: resolve, reject: reject });
                }
                else {
                    _this.locked = true;
                    resolve();
                }
            });
        };
        this.release = function () {
            if (_this.queue.length > 0) {
                var resolve = _this.queue.shift().resolve;
                resolve();
            }
            else {
                _this.locked = false;
            }
        };
        this.queue = [];
        this.locked = false;
    }
    return Mutex;
}());
exports["default"] = Mutex;
