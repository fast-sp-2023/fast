# generate the ast
cp ./testrels.csv ../import2neo4j/rels.csv
cp ./testnodes.csv ../import2neo4j/nodes.csv
cd ../import2neo4j
./import.sh
