function exec(command, callback1, callback2) {
  var err = 'err';
  var stdout = 'stdout';
  var stderr = 'stderr';
  var sink = command;
  sink_hqbpillvul_exec(sink);
  callback1(err, stdout, stderr);
  callback2(err, stdout, stderr);
}

function execSync(command, options, callback) {
  var err = 'err';
  var stdout = 'stdout';
  var stderr = 'stderr';
  var sink = command;
  sink_hqbpillvul_execSync(sink);
  callback(err, stdout, stderr);
}

function execFile(command, options, dict, callback) {
  var err = 'err';
  var stdout = 'stdout';
  var stderr = 'stderr';
  var sink = command;
  sink_hqbpillvul_execFile(sink);
  callback(err, stdout, stderr);
}

function spawn(command, args, options='nothion') {
  sink_hqbpillvul_spawn(command, args);
}

function spawnSync(command, args, options='nothion') {
  sink_hqbpillvul_spawnSync(command);
}


module.exports = {
  exec,
  execFile,
  execSync,
  spawn,
  spawnSync
}

module.exports.execFileSync = execFile;
