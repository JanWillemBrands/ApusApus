rem call %arthome%\grammarWrite buildJLS18\jls18.art
call %arthome%\grammarWrite otherGrammars\jls18bnfV3.art
call %arthome%\parseGLL ARTCharacterGrammar.art jfxSourceFlatCompressed\AABalanceFlipTest.java
call %arthome%\artV3TestGenerated jfxSourceFlatCompressed\BidiApp.java
rem del art*.art
rem del artGenerated*.java
