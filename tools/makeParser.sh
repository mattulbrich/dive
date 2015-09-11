# run this in main dir of project

dir=src/edu/kit/iti/algover/parser
antlr=`pwd`/antlr.jar

cd $dir

/usr/lib/jvm/java-7-oracle/bin/java -jar $antlr Dafny.g && echo "Parser successfully created"
