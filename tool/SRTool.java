package tool;
import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import ast.*;
import ast.visitor.impl.DefaultVisitor;
import ast.visitor.impl.LoopSummarisationVisitor;
import ast.visitor.impl.PrintVisitor;
import ast.visitor.impl.ShadowVisitor;
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

		// convert ANTLR Program node to our own type of Program node
		Program program = (Program) new AntlrToAstConverter().visit(ctx);

		// apply loop summarisation
		program = (Program) new LoopSummarisationVisitor().visit(program);
		debugUtil.print("Code after loop summarisation is applied:\n" + new PrintVisitor().visit(program));

		// apply variable shadow removal
		program = (Program) new ShadowVisitor(program).visit(program);
		debugUtil.print("Code after shadow visiting is applied:\n" + new PrintVisitor().visit(program));

		//assert ctx.procedures.size() == 1; // For Part 1 of the coursework, this can be assumed
		// Check each procedure by applying summarisation techniques for any method calls
		for(ProcedureDecl proc : program.getProcedureDecls()) {
			VCGenerator vcgen = new VCGenerator(program, proc, debugUtil);
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
