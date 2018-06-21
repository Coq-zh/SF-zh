Preface.vo Preface.glob Preface.v.beautified: Preface.v
Preface.vio: Preface.v
Basics.vo Basics.glob Basics.v.beautified: Basics.v
Basics.vio: Basics.v
Induction.vo Induction.glob Induction.v.beautified: Induction.v Basics.vo
Induction.vio: Induction.v Basics.vio
Lists.vo Lists.glob Lists.v.beautified: Lists.v Induction.vo
Lists.vio: Lists.v Induction.vio
Poly.vo Poly.glob Poly.v.beautified: Poly.v Lists.vo
Poly.vio: Poly.v Lists.vio
Tactics.vo Tactics.glob Tactics.v.beautified: Tactics.v Poly.vo
Tactics.vio: Tactics.v Poly.vio
Logic.vo Logic.glob Logic.v.beautified: Logic.v Tactics.vo
Logic.vio: Logic.v Tactics.vio
IndProp.vo IndProp.glob IndProp.v.beautified: IndProp.v Logic.vo
IndProp.vio: IndProp.v Logic.vio
Maps.vo Maps.glob Maps.v.beautified: Maps.v
Maps.vio: Maps.v
ProofObjects.vo ProofObjects.glob ProofObjects.v.beautified: ProofObjects.v IndProp.vo
ProofObjects.vio: ProofObjects.v IndProp.vio
IndPrinciples.vo IndPrinciples.glob IndPrinciples.v.beautified: IndPrinciples.v ProofObjects.vo
IndPrinciples.vio: IndPrinciples.v ProofObjects.vio
Rel.vo Rel.glob Rel.v.beautified: Rel.v IndProp.vo
Rel.vio: Rel.v IndProp.vio
Imp.vo Imp.glob Imp.v.beautified: Imp.v Maps.vo
Imp.vio: Imp.v Maps.vio
ImpParser.vo ImpParser.glob ImpParser.v.beautified: ImpParser.v Maps.vo Imp.vo
ImpParser.vio: ImpParser.v Maps.vio Imp.vio
ImpCEvalFun.vo ImpCEvalFun.glob ImpCEvalFun.v.beautified: ImpCEvalFun.v Imp.vo Maps.vo
ImpCEvalFun.vio: ImpCEvalFun.v Imp.vio Maps.vio
Extraction.vo Extraction.glob Extraction.v.beautified: Extraction.v ImpCEvalFun.vo Imp.vo ImpParser.vo Maps.vo
Extraction.vio: Extraction.v ImpCEvalFun.vio Imp.vio ImpParser.vio Maps.vio
Auto.vo Auto.glob Auto.v.beautified: Auto.v Maps.vo Imp.vo
Auto.vio: Auto.v Maps.vio Imp.vio
Postscript.vo Postscript.glob Postscript.v.beautified: Postscript.v
Postscript.vio: Postscript.v
Bib.vo Bib.glob Bib.v.beautified: Bib.v
Bib.vio: Bib.v
PrefaceTest.vo PrefaceTest.glob PrefaceTest.v.beautified: PrefaceTest.v Preface.vo
PrefaceTest.vio: PrefaceTest.v Preface.vio
BasicsTest.vo BasicsTest.glob BasicsTest.v.beautified: BasicsTest.v Basics.vo
BasicsTest.vio: BasicsTest.v Basics.vio
InductionTest.vo InductionTest.glob InductionTest.v.beautified: InductionTest.v Induction.vo
InductionTest.vio: InductionTest.v Induction.vio
ListsTest.vo ListsTest.glob ListsTest.v.beautified: ListsTest.v Lists.vo
ListsTest.vio: ListsTest.v Lists.vio
PolyTest.vo PolyTest.glob PolyTest.v.beautified: PolyTest.v Poly.vo
PolyTest.vio: PolyTest.v Poly.vio
TacticsTest.vo TacticsTest.glob TacticsTest.v.beautified: TacticsTest.v Tactics.vo
TacticsTest.vio: TacticsTest.v Tactics.vio
LogicTest.vo LogicTest.glob LogicTest.v.beautified: LogicTest.v Logic.vo
LogicTest.vio: LogicTest.v Logic.vio
IndPropTest.vo IndPropTest.glob IndPropTest.v.beautified: IndPropTest.v IndProp.vo
IndPropTest.vio: IndPropTest.v IndProp.vio
MapsTest.vo MapsTest.glob MapsTest.v.beautified: MapsTest.v Maps.vo
MapsTest.vio: MapsTest.v Maps.vio
ProofObjectsTest.vo ProofObjectsTest.glob ProofObjectsTest.v.beautified: ProofObjectsTest.v ProofObjects.vo
ProofObjectsTest.vio: ProofObjectsTest.v ProofObjects.vio
IndPrinciplesTest.vo IndPrinciplesTest.glob IndPrinciplesTest.v.beautified: IndPrinciplesTest.v IndPrinciples.vo
IndPrinciplesTest.vio: IndPrinciplesTest.v IndPrinciples.vio
RelTest.vo RelTest.glob RelTest.v.beautified: RelTest.v Rel.vo
RelTest.vio: RelTest.v Rel.vio
ImpTest.vo ImpTest.glob ImpTest.v.beautified: ImpTest.v Imp.vo
ImpTest.vio: ImpTest.v Imp.vio
ImpParserTest.vo ImpParserTest.glob ImpParserTest.v.beautified: ImpParserTest.v ImpParser.vo
ImpParserTest.vio: ImpParserTest.v ImpParser.vio
ImpCEvalFunTest.vo ImpCEvalFunTest.glob ImpCEvalFunTest.v.beautified: ImpCEvalFunTest.v ImpCEvalFun.vo
ImpCEvalFunTest.vio: ImpCEvalFunTest.v ImpCEvalFun.vio
ExtractionTest.vo ExtractionTest.glob ExtractionTest.v.beautified: ExtractionTest.v Extraction.vo
ExtractionTest.vio: ExtractionTest.v Extraction.vio
AutoTest.vo AutoTest.glob AutoTest.v.beautified: AutoTest.v Auto.vo
AutoTest.vio: AutoTest.v Auto.vio
PostscriptTest.vo PostscriptTest.glob PostscriptTest.v.beautified: PostscriptTest.v Postscript.vo
PostscriptTest.vio: PostscriptTest.v Postscript.vio
BibTest.vo BibTest.glob BibTest.v.beautified: BibTest.v Bib.vo
BibTest.vio: BibTest.v Bib.vio
