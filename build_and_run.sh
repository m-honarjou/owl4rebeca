gradle distZip -Pdisable-pandoc
# gradle distZip -Pdisable-pandoc -Dorg.gradle.dependency.verification=off
rm -rf build/distributions/owl-jre-22.0-development/
unzip build/distributions/owl-jre-22.0-development.zip -d build/distributions
./build/distributions/owl-jre-22.0-development/bin/owl

