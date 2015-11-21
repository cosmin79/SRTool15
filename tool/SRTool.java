package tool;
import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

import ast.*;
import ast.visitor.impl.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import util.ProcessExec;
import util.ProcessTimeoutException;

public class SRTool {

	public static final String BIN_DIR = "execBin";

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
		File binDir = new File(BIN_DIR);
		if (!binDir.exists()) {
			binDir.mkdir();
		}

		String fileContent = readFile(args[0], StandardCharsets.UTF_8);
		String relativePathTest = args[0].replaceAll("/", "_");
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
		program = (Program) new DefaultVisitor(new HashMap<>()).visit(program);

		// This execution plan object will attempt to try multiple strategies before deciding
		new ExecutionPlan(program, debugUtil, relativePathTest).verifyProgram();
	}
}
