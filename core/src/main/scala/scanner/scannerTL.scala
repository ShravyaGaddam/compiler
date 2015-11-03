/*
 * scannerTL.scala
 * CS5363-E
 * Spring 2015
 * Amulya Battu
 * Gabe Fernandez
 * Shravya Gaddam
 * David Holland
 */
package scanner

import parser.ParserTL

import scala.collection.mutable.ArrayBuffer
import scala.io.Source

object scannerTL {

  //lexical analysis of each line. Splits each line up into words
  //separated by white spaces and associates a token type for each word.
  //words that cannot be identified as a token cause a LexicalError to be thrown.
  //returns an array of tokens , throws a ScannerException
  def tokenizeLine(line: String): Array[ParserTL.Token] = {
    var tokens = ArrayBuffer[ParserTL.Token]()
    var words: Array[String] = new Array[String](10)

    //1)SPLIT THE LINE INTO AN ARRAY OF WORDS
    //words = line.split("[\\p{Punct}\\s]+")
    words = line.split("[\\s]+")
    val identifier = "[A-Z][A-Z0-9]*".r //regex for identifier
    val number = "[1-9][0-9]*|0".r //regex for number

    var word: String = ""

    try {
      //2) Classify each word as a token type and add it the the list
      for (word <- words) {
        word match {
          case "%" => throw new ParserTL.DoneException("done") //break if comment symbol seen
          case "var" => tokens += ParserTL.VAR
          case "as" => tokens += ParserTL.AS
          case identifier() => tokens += ParserTL.Ident(word) //MATCH THE WORD AGAINST REG EXP
          case number() => tokens += ParserTL.Num(word.toInt)
          case "int" => tokens += ParserTL.INT
          case "bool" => tokens += ParserTL.BOOL
          case "writeInt" => tokens += ParserTL.WRITEINT
          case "readInt" => tokens += ParserTL.READINT
          case ";" => tokens += ParserTL.SC
          case ":=" => tokens += ParserTL.ASGN
          case "+" | "-" => tokens += ParserTL.ADDITIVE(word)
          case "*" | "div" | "mod" => tokens += ParserTL.MULTIPLICATIVE(word)
          case "=" | "!=" | "<" | ">" | "<=" | ">=" => tokens += ParserTL.COMPARE(word)
          case "true" | "false" => tokens += ParserTL.Boollit(word)
          case "if" => tokens += ParserTL.IF
          case "then" => tokens += ParserTL.THEN
          case "else" => tokens += ParserTL.ELSE
          case "begin" => tokens += ParserTL.BEGIN
          case "end" => tokens += ParserTL.END
          case "while" => tokens += ParserTL.WHILE
          case "do" => tokens += ParserTL.DO
          case "program" => tokens += ParserTL.PROGRAM
          case "(" => tokens += ParserTL.LP
          case ")" => tokens += ParserTL.RP
          case "" => Unit //throw out an empty line
          case _ => throw new ParserTL.ScannerException("Unrecognized symbol: \"" + word +
            "\" in: " + line)
        } // end match
      } // end for
    } catch {
      case d: ParserTL.DoneException => Unit
    } // end try

    return tokens.toArray
  } //end tokenizeLine

  //write a function that calls tokenizeLine for every line in the program file
  //input. Collect all the tokens, preserving their lexical order, into one big 
  //big list of tokens. Then finally pass this list of tokens to the parser 
  //to read as its input. Throws ScannerException which must be caught by caller
  def tokenizer(source: Source): List[ParserTL.Token] = {

    var tokens = ArrayBuffer[ParserTL.Token]()
    var lineNum: Int = 1
    for (line <- source.getLines) {
      try {
        //TODO - check this is appending correctly
        val L = tokenizeLine(line)
        tokens ++= tokenizeLine(line) //append list to tail of tokens list
      }
      catch {
        case e: ParserTL.ScannerException => {
          println("tokenizer() SCANNER Error line " + lineNum + ": " + e.getMessage)
          throw e //re-throw error
        }
      } // end try
      lineNum += 1
    } // end for

    return tokens.toList
  } // end tokenizer


  def main(argv: Array[String]) {

    //open input file
    val file: String = "tl-progs/simple1.tl"
    // val file : String = "tl-progs/euclid.tl"
    //val file : String = "tl-progs/type-error1.tl"
    val source = Source.fromFile(file)

    try {
      var listOfTokens = tokenizer(source)
      println("LIST OF TOKENS for file " + file)
      for (token <- listOfTokens)
        print(token.toString() + " ")
    }
    catch {
      case e: ParserTL.ScannerException => {
        println("SCANNER Error: " + e.getMessage)
      }
      case e: Exception => {
        println("SCANNER Error: " + e.getMessage)
      }
    } // end try

  } // end main

}

//end scannerTL