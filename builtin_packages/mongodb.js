module.exports.MongoClient = function MongoClient(url, options, callback){
}

module.exports.MongoClient.prototype.connect = function (callback){
    if (callback){
        callback(null, this);
    } else {
        return new Promise(function(resolve, reject){
            resolve(this);
        });
    }
}

module.exports.MongoClient.connect = function (url, options, callback){
    var mongoClient = new MongoClient();
    if (typeof options === 'function'){
        return mongoClient.connect(options);
    } else {
        return mongoClient.connect(callback);
    }
}

module.exports.MongoClient.prototype.db = function (dbName, options){
    return new Db(dbName, options);
}

module.exports.Db = function Db(databaseName, topology, options){
    sink_hqbpillvul_nosql(databaseName);
}

Db.prototype.collection = function(name, options, callback) {
    var collection = new Collection();
    if (typeof options === 'function'){
        options(null, collection);
    } else if (typeof callback === 'function'){
        callback(null, collection);
    } else {
        return new Promise(function(resolve, reject){
            resolve(collection);
        });
    }
}

Db.prototype.collection = function(options, callback) {
    var collection = new Collection();
    if (typeof options === 'function'){
        options(null, [collection]);
    } else if (typeof callback === 'function'){
        callback(null, [collection]);
    } else {
        return new Promise(function(resolve, reject){
            resolve([collection]);
        });
    }
}

module.exports.Collection = function Collection(){
}

Collection.prototype.aggregate = function(pipeline, options, callback){
    if (typeof pipeline === 'function'){
        pipeline(null, null);
    } else {
        sink_hqbpillvul_nosql(pipeline);
    }
    if (typeof options === 'function'){
        options(null, null);
    } else {
        sink_hqbpillvul_nosql(options);
    }
    if (typeof callback === 'function'){
        callback(null, null);
    };
}

Collection.prototype.insert = function (docs, options, callback){
    if (Array.isArray(docs)){
        this.insertMany(docs);
    } else {
        this.insertOne(docs);
    }
}

Collection.prototype.insertOne = function (doc, options, callback){
    sink_hqbpillvul_nosql(doc);
    sink_hqbpillvul_nosql(options);
    callback();
}

Collection.prototype.insertMany = function (docs, options, callback){
    for (let doc of docs){
        sink_hqbpillvul_nosql(doc);
    }
    sink_hqbpillvul_nosql(options);
    callback();
}

Collection.prototype.update = Collection.prototype.updateOne = Collection.prototype.updateMany =
function (filter, update, options, callback){
    sink_hqbpillvul_nosql(filter);
    sink_hqbpillvul_nosql(update);
    if (typeof options === 'function'){
        options();
    }
    if (typeof callback === 'function'){
        callback();
    }
}

Collection.prototype.find = Collection.prototype.findOne = function (query, options, callback){
    sink_hqbpillvul_nosql(query);
    sink_hqbpillvul_nosql(options);
    if (typeof callback === 'function'){
        callback();
    }
}