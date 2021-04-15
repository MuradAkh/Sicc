'use-strict';
console.log("STARTING TOOL....");
var exec = require('util').promisify(require('child_process').exec);
var tools = require("./utils");
var yargs = require("yargs")
    .demandOption("file")
    .option("ua")
    .option("v2")
    .option("sync");
var filename = yargs.argv.file;
var solver = yargs.argv.ua ? "ua" : "cbmc";
tools.cleanUp()
    .then(tools.createWorkdir)
    .then(function () { return tools.verify(filename, solver, yargs.argv.sync); })
    .then(JSON.stringify)
    .then(console.log)["catch"](console.error);
