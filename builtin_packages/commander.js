var _this = module.exports;
function option(str) {
  return _this;
}

function action(cb) {
  OPGen_markTaintCall(cb);
}

function command(comd) {
  return _this;
}
function description(str) {
  return _this;
}

function commander() {
  return _this;
}

_this.command = command;
_this.description = description;
_this.option = option;
_this.action = action;
