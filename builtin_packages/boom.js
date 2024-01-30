exports.Boom = function Boom(message, options = {}){
    sink_hqbpillvul_http_write(message);
    sink_hqbpillvul_http_write(options);
};
exports.isBoom = function (){
    return true;
};
exports.badRequest = function (message, data) {
    return new exports.Boom(message, { statusCode: 400, data, ctor: exports.badRequest });
};