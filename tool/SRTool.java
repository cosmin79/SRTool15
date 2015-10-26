package tool;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import util.ProcessExec;
import util.ProcessTimeoutException;

public class SRTool {

    private static final int TIMEOUT = 30;

	public static void main(String[] args) throws IOException, InterruptedException {
        String filename = args[0];
		// useful abstraction for debug prints
		DEBUG_LEVEL debugLevel;
		if (args.length >= 2) {
			debugLevel = Boolean.parseBoolean(args[1]) ? DEBUG_LEVEL.TESTING : DEBUG_LEVEL.PROD;
		} else {
			debugLevel = DEBUG_LEVEL.PROD;
		}
		DebugUtil debugUtil = new DebugUtil(debugLevel);

		ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
        SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		ProgramContext ctx = parser.program();
		if(parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}

		Typechecker tc = new Typechecker();
		tc.visit(ctx);
		tc.resolve();
		if(tc.hasErrors()) {
			System.err.println("Errors were detected when typechecking " + filename + ":");
			for(String err : tc.getErrors()) {
				System.err.println("  " + err);
			}
			System.exit(1);
		}

		// create a new handler for variable ids that is going to be shared across classes
		VariableIdsGenerator idsGenerator = new VariableIdsGenerator();

		// record the global variables here in a stack (all those variables have id 0 initially)
		Map<String, Integer> globalsStack = new HashMap<>();
		for(SimpleCParser.VarDeclContext varDecl : ctx.globals) {
			String varName = varDecl.ident.name.getText();
			globalsStack.put(varName, idsGenerator.generateFresh(varName));
		}

		//assert ctx.procedures.size() == 1; // For Part 1 of the coursework, this can be assumed
		// Check each procedure by applying summarisation techniques for any method calls
		for(ProcedureDeclContext proc : ctx.procedures) {
			VCGenerator vcgen = new VCGenerator(proc, globalsStack, idsGenerator, debugUtil);
			String vc = vcgen.generateVC().toString();

			ProcessExec process = new ProcessExec("./z3", "-smt2", "-in");
			String queryResult = "";
			try {
				queryResult = process.execute(vc, TIMEOUT);
			} catch (ProcessTimeoutException e) {
				System.out.println("UNKNOWN");
				System.exit(1);
			}
			
			if (queryResult.startsWith("sat")) {
				System.out.println("INCORRECT");
				System.exit(0);
			}
			
			if (!queryResult.startsWith("unsat")) {
				System.out.println("UNKNOWN");
				System.out.println(queryResult);
				System.exit(1);
			}
		}
		
		System.out.println("CORRECT");
		System.exit(0);
		
    }
}
