rm -rf build/distributions/owl-jre-22.0-development/
unzip -q build/distributions/owl-jre-22.0-development.zip -d build/distributions
echo running: DiningPhilosophers
./build/distributions/owl-jre-22.0-development/bin/owl rebeca2nba -i DiningPhilosophers.rebeca -i DiningPhilosophers.property --run-in-non-native-mode
echo running: GeneralCoreRebecaModelWithInitialMethod
./build/distributions/owl-jre-22.0-development/bin/owl rebeca2nba -i CoreRebecaModelWithInitialMethod.rebeca -i GeneralCoreRebecaModelWithInitialMethod.property --run-in-non-native-mode
echo running: CoreRebecaModelWithInitialMethod
./build/distributions/owl-jre-22.0-development/bin/owl rebeca2nba -i CoreRebecaModelWithInitialMethod.rebeca -i CoreRebecaModelWithInitialMethod.property --run-in-non-native-mode
