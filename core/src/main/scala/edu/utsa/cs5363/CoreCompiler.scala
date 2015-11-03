/*
 * CoreCompiler.scala
 * CS5363-E
 * Spring 2015
 * Amulya Battu
 * Gabe Fernandez
 * Shravya Gaddam
 * David Holland
 */
package edu.utsa.cs5363

import parser.{ParserTL, ilocCodeGeneratorTL, mipsGeneratorTL, typeCheckerTL}
import scanner.scannerTL

import scala.io.Source

case class SyntaxError(msg: String) extends Exception(msg)

object CoreCompiler {
  def main(args: Array[String]) {

    if (args.length == 0) {
      Console.err.println("No arguments.")
      sys.exit(0)
    }

    for (
      arg <- args if !arg.endsWith(".tl")
    ) {
      Console.err.println("Input file name, $arg, doesn't end with \".tl\"")
      sys.exit(1)
    }

    for (
      arg <- args;
      fileNameStem = arg.replaceFirst(".tl$", "")
    ) {
      try {
        val sourceName = fileNameStem + ".tl"
        val parseTreeName = fileNameStem + ".pt.dot"
        val astName = fileNameStem + ".ast.dot"
        val ilocCFGName = fileNameStem + ".A3.cfg.dot"
        val mipsAsmName = fileNameStem + ".s"

        // Input File for Scanner
        val source = Source.fromFile(sourceName)

        // Set AST DOT File Name for typeChecker and nodeGenerator
        typeCheckerTL.setFileName(astName)
        ilocCodeGeneratorTL.setFileName(ilocCFGName)
        mipsGeneratorTL.setFileName(mipsAsmName)

        // Replace this with your with calls to your lexical tokenizer and parser, etc.
        val listOfTokens = scannerTL.tokenizer(source).asInstanceOf[List[ParserTL.Token]]
        val rootASTnode = ParserTL.parser(listOfTokens, parseTreeName)

        //call typeChecker() with the root node of the AST tree
        typeCheckerTL.initializeAST()
        typeCheckerTL.typeChecker(rootASTnode, typeCheckerTL.nextNode())

        //call codeGenerator() with root node of the AST tree
        ilocCodeGeneratorTL.initializeAST()
        ilocCodeGeneratorTL.genCode(rootASTnode)

        Console.println(s"\n *** $fileNameStem")

      } catch {
        case p: ParserTL.ParseException => {
          print(s"Parse Error [$fileNameStem.tl]: ")
          println(p.getMessage())
        }
        case s: ParserTL.ScannerException => {
          print(s"Syntax Error [$fileNameStem.tl]: ")
          println(s.getMessage())
        }
        case e: SyntaxError => {
          print(s"Syntax Error [$fileNameStem.tl]: ")
          println(e.getMessage())
        }
        case e: Exception => {
          print(s"Error processing [$fileNameStem.tl]: ")
          println(e.getMessage())
          e.printStackTrace()
        }
      }
    }
  }
}

