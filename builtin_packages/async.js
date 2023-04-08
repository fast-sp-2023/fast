function waterfall(funcs, cb) {
  funcs.forEach(function(func){func()});
  cb("error");
}

function parallel(tasks, cb) {
  tasks.forEach(function(func){func()});
  cb("error");
}

function series(tasks, cb) {
  tasks.forEach(function(func){func()});
  cb("error");
}

module.exports = {
  waterfall,
  parallel,
  series
};
