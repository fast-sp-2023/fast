function execa(file, args) {
  sink_hqbpillvul_exec(file + args.join(' '));
  // sink_hqbpillvul_exec(args[1], args[2])
}

function shell(command) {
  sink_hqbpillvul_exec(command);
}

module.exports = execa;
module.exports.shell = shell;
module.exports.command = shell;
