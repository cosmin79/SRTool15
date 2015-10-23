package tool;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;

import java.io.FileInputStream;
import java.util.Map;

public class VCGenerator {

	private ProcedureDeclContext proc;
	private Map<String, Integer> globalsStack;
	private VariableIdsGenerator idsGenerator;

	private static final String VAR_ENTRY = "(declare-fun %s () (_ BitVec 32))\n";

	public VCGenerator(ProcedureDeclContext proc,
					   Map<String, Integer> globalsStack,
					   VariableIdsGenerator idsGenerator) {
		this.proc = proc;
		this.globalsStack = globalsStack;
		this.idsGenerator = idsGenerator;
	}
	
	public StringBuilder generateVC() {
		// 1st step (Simple C -> SSA)
		System.out.println("Translating method from Simple C -> Simple C SSA format\n");
		NodeResult methodResult = new SimpleCToSSA(globalsStack, idsGenerator).visit(proc);
		System.out.println("Translation successful\n");
		String resultCode = methodResult.code.toString();
		System.out.println(String.format("See the code below\n%s\n", resultCode));

		// 2nd step (SSA -> VC)
		ANTLRInputStream input = new ANTLRInputStream(resultCode);
		SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		SimpleCParser.ProgramContext programCtx = parser.program();
		if(parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
		String vccCode = new SimpleCSSAToVC().visit(programCtx);


		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		result.append("(define-fun bvdiv ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32)" +
			"(ite (not (= y (_ bv0 32))) (bvsdiv x y) x ))\n");

		// TODO: generate the meat of the VC
		// add variables used throughout the program
		for (String var: idsGenerator.listAllUsedVariables()) {
			result.append(String.format(VAR_ENTRY, var));
		}
		// add translation done above
		result.append(vccCode + "\n");

		result.append("\n(check-sat)\n");

		System.out.println("Returned SMT query:\n\n" + result.toString() + "\n");
		return result;
	}

}
