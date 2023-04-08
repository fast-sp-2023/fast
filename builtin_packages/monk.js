module.exports = function (uri, options, callback){
    return new Manager(uri, options, callback);
}

module.exports.Manager = function Manager(uri, options, callback){
    callback();
}

module.exports.Manager.prototype.get = function (name, options){
    return new Collection();
}

module.exports.Collection = function Collection(){
}

module.exports.Collection.prototype.insert = module.exports.Collection.prototype.insertMany = function (docs, options, callback){
    sink_hqbpillvul_nosql(docs);
    for (let i of docs){
        sink_hqbpillvul_nosql(i);
    }
    callback();
}

module.exports.Collection.prototype.insertOne = function (doc, options, callback){
    sink_hqbpillvul_nosql(doc);
    callback();
}

module.exports.Collection.prototype.update = function (selector, update, options, callback){
    sink_hqbpillvul_nosql(update);
    callback();
}

module.exports.Collection.prototype.updateMany = module.exports.Collection.prototype.updateOne = function (filter, update, options, callback){
    sink_hqbpillvul_nosql(update);
    callback();
}