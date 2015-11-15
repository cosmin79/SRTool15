package tool;
import ast.BlockStmt;
import ast.ProcedureDecl;
import ast.Program;
import ast.visitor.impl.PrintVisitor;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;

import java.io.FileInputStream;
import java.util.Map;

public class VCGenerator {

	private Program program;
	private ProcedureDecl proc;
	private Map<String, Integer> globalsStack;
	private VariableIdsGenerator idsGenerator;
	private DebugUtil debugUtil;

	private static final String VAR_ENTRY = "(declare-fun %s () (_ BitVec 32))\n";

	public VCGenerator(Program program,
					   ProcedureDecl proc,
					   Map<String, Integer> globalsStack,
					   VariableIdsGenerator idsGenerator,
					   DebugUtil debugUtil) {
		this.program = program;
		this.proc = proc;
		this.globalsStack = globalsStack;
		this.idsGenerator = idsGenerator;
		this.debugUtil = debugUtil;
	}
	
	public StringBuilder generateVC() {
		// Transform method to SSA
		BlockStmt ssaBlock = (BlockStmt) new SSAVisitor(program, idsGenerator).visit(proc);
		debugUtil.print("Result after SSA visitor:\n" + new PrintVisitor().visit(ssaBlock));

		// this visitor generates SMT code
		VCCVisitor visitorGen = new VCCVisitor();
		ssaBlock.accept(visitorGen);
		String vccCode = visitorGen.getSmtResult();

		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		result.append("(define-fun bvdiv ((x (_ BitVec 32)) (y (_ BitVec 32))) (_ BitVec 32)" +
			"(ite (not (= y (_ bv0 32))) (bvsdiv x y) x ))\n");

		// add variables used throughout the program
		for (String var: idsGenerator.listAllUsedVariables()) {
			result.append(String.format(VAR_ENTRY, var));
		}
		// add translation done above
		result.append(vccCode + "\n");

		result.append("\n(check-sat)\n");

		debugUtil.print("Returned SMT query:\n\n" + result.toString() + "\n");
		return result;
	}

}
