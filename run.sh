rm -rf build/distributions/owl-jre-22.0-development/
unzip -q build/distributions/owl-jre-22.0-development.zip -d build/distributions
echo running: DiningPhilosophers
./build/distributions/owl-jre-22.0-development/bin/owl  rebeca2ltl DiningPhilosophers.rebeca DiningPhilosophers.property printModel
echo running: GeneralCoreRebecaModelWithInitialMethod
./build/distributions/owl-jre-22.0-development/bin/owl  rebeca2ltl CoreRebecaModelWithInitialMethod.rebeca GeneralCoreRebecaModelWithInitialMethod.property printModel
echo running: CoreRebecaModelWithInitialMethod
./build/distributions/owl-jre-22.0-development/bin/owl  rebeca2ltl CoreRebecaModelWithInitialMethod.rebeca CoreRebecaModelWithInitialMethod.property printModel
echo running: test t1.png
./build/distributions/owl-jre-22.0-development/bin/owl  testrebeca2ltl
