package tool;
import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
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

    private static final int TIMEOUT = 10;

	private static String readFile(String path, Charset encoding) throws IOException {
		byte[] encoded = Files.readAllBytes(Paths.get(path));
		return new String(encoded, encoding);
	}

	private static String simpleCToNoVarShadowing(String programString) throws  IOException {
		ANTLRInputStream input = new ANTLRInputStream(programString);
		SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		SimpleCParser.ProgramContext programCtx = parser.program();
		if(parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
		String result = new SimpleCToNoShadowing(new VariableIdsGenerator()).visit(programCtx);

		return result;
	}

	private static ProgramContext syntaxAndSemanticProgramCheck(String programString) {
		ANTLRInputStream input = new ANTLRInputStream(programString);
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
			System.err.println("Errors were detected when typechecking the program:");
			for(String err : tc.getErrors()) {
				System.err.println("  " + err);
			}
			System.exit(1);
		}

		return ctx;
	}

	public static void main(String[] args) throws IOException, InterruptedException {
		String fileContent = readFile(args[0], StandardCharsets.UTF_8);
		ProgramContext ctx = syntaxAndSemanticProgramCheck(fileContent);

		// useful abstraction for debug prints
		DEBUG_LEVEL debugLevel;
		if (args.length >= 2) {
			debugLevel = Boolean.parseBoolean(args[1]) ? DEBUG_LEVEL.TESTING : DEBUG_LEVEL.PROD;
		} else {
			debugLevel = DEBUG_LEVEL.PROD;
		}
		DebugUtil debugUtil = new DebugUtil(debugLevel);

		debugUtil.print("Preparing to apply 1st transformation that removes variable shadowing");
		String simpleCNoVarShadowingProgram = simpleCToNoVarShadowing(fileContent);

		debugUtil.print("Result:\n" + simpleCNoVarShadowingProgram);
		debugUtil.print("Make sure the program is still correct from a syntactic and semantic point of view");
		ctx = syntaxAndSemanticProgramCheck(simpleCNoVarShadowingProgram);

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
