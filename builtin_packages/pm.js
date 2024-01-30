exports.createMaster = function (options) {
    var Master = function(){};
    Master.prototype.register = function (name, file, options, argv) {
        require(file);
        sink_hqbpillvul_exec(file);
        sink_hqbpillvul_exec(argv.join(' '));
    }
    return new Master();
};

