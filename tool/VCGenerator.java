package tool;
import ast.*;
import ast.visitor.impl.PrintVisitor;

import java.util.*;

class VCResult {

	private String query;

	// Remember the last line in the SMT query is of the form:
	// (assert (not (and cond1 cond2 .. condK)), where condI comes from an assert condition
	// this map matches condI to the right AssertNode in the last AST
	private Map<String, AssertStmt> booleanToAssert;

	public VCResult(String query, Map<String, AssertStmt> booleanToAssert) {
		this.query = query;
		this.booleanToAssert = booleanToAssert;
	}

	public String getQuery() {
		return query;
	}

	public Map<String, AssertStmt> getBooleanToAssert() {
		return booleanToAssert;
	}
}

public class VCGenerator {

	private static final String SPACE = " ";

	private static final String VAR_ENTRY = "(declare-fun %s () (_ BitVec 32))\n";

	private static final String BOOL_VAR_ENTRY = "(declare-fun %s () Bool)\n";

	private static final String ASSERT_BOOLEAN = "(assert (= %s %s))\n";

	private static final String BOOL_NAME = "prop";

	private static final String NOT_AND_ASSERT = "(assert (not (and %s)))\n";

	private static final String NOT_ASSERT = "(assert (not %s))\n";

	private Program program;

	private ProcedureDecl proc;

	private DebugUtil debugUtil;

	private Map<Node, Node> predMap;

	public VCGenerator(Program program,
					   ProcedureDecl proc,
					   DebugUtil debugUtil,
					   Map<Node, Node> predMap) {
		this.program = program;
		this.proc = proc;
		this.debugUtil = debugUtil;
		this.predMap = predMap;
	}
	
	public VCResult generateVC() {
		// Transform method to SSA
		VariableIdsGenerator idsGenerator = new VariableIdsGenerator();
		BlockStmt ssaBlock = (BlockStmt) new SSAVisitor(predMap, program, idsGenerator).visit(proc);
		debugUtil.print("Result after SSA visitor:\n" + new PrintVisitor().visit(ssaBlock));

		// this visitor generates SMT code
		VCCVisitor visitorGen = new VCCVisitor();
		ssaBlock.accept(visitorGen);

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

		// add facts known
		for (String fact: visitorGen.getFacts()) {
			result.append(fact);
		}

		// add boolean variable declarations
		Map<String, String> booleanToCond = new LinkedHashMap<>();
		Map<String, AssertStmt> booleanToAssert = new LinkedHashMap<>();
		for (Map.Entry<AssertStmt, String> entryAssert: visitorGen.getAssertConditions().entrySet()) {
			String newVar = String.format("%s%d", BOOL_NAME, idsGenerator.generateFresh(BOOL_NAME));
			result.append(String.format(BOOL_VAR_ENTRY, newVar));
			booleanToCond.put(newVar, entryAssert.getValue());
			booleanToAssert.put(newVar, entryAssert.getKey());
		}

		// match boolean variables with assertions
		for (Map.Entry<String, String> entry: booleanToCond.entrySet()) {
			result.append(String.format(ASSERT_BOOLEAN, entry.getKey(),
					String.format(SmtUtil.TO_BOOL_EXPR, entry.getValue())));
		}

		// space separated cond
		StringBuilder sb = new StringBuilder();
		for (String boolCond: booleanToCond.keySet()) {
			sb.append(boolCond + SPACE);
		}
		String spaceSepCond = sb.toString();

		// add final cond
		if (booleanToCond.isEmpty()) {
			result.append(String.format(NOT_ASSERT, "true"));
		} else {
			result.append(String.format(NOT_AND_ASSERT, "true " + spaceSepCond));
		}

		result.append("\n(check-sat)\n");
		if (!booleanToCond.isEmpty()) {
			result.append(String.format("(get-value (%s))\n", spaceSepCond));
		}

		debugUtil.print("Returned SMT query:\n\n" + result.toString() + "\n");

		return new VCResult(result.toString(), booleanToAssert);
	}

}
