// util.js
const childProcess = require("child_process");
const logger = require("./logger");
function promisify(fn) {
 return function (arg) {
  return new Promise(function executor(resolve, reject) {
    fn(arg, function cb(err, res) {
        if (err != null) return reject(err);
        resolve(res);
    });
  });
 };
}
function execProcess(method){
  // simpilifed from child-process-promise
  return promisify(childProcess[method]);
}
async function anotherAlg(options) { 
  // a complex compression algorithm causing state explosion of abstract interpretation 
}
async function compress(options) {
 switch (options.alg) {
  case 'foo':
    return await anotherAlg(options);
  case 'xz':
    var command = ["xz", "--stdout", "-k"].join(" ");
    logger.log(`xz, ${options.path}`);
    if (!options.path)
      command += "data";
    else
      command += options.path;
    return await execProcess("exec")(command);
 }
}
module.exports = function Util() { };
module.exports.prototype.compress = compress;