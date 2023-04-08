const madge = require('madge');
var package_path = process.argv[2];
madge(package_path, includeNpm=false)
  .then((res) => {
    //res.image('./image.png');
    console.dir( res.orphans(), {'maxArrayLength': null} );
  });
