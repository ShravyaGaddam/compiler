/*
 *  * typeCheckerTL.scala
 * CS5363-E
 * Spring 2015
 * Amulya Battu
 * Gabe Fernandez
 * Shravya Gaddam
 * David Holland
 */
package parser

import java.io._

import parser.ParserTL._

import scala.collection.mutable.ArrayBuffer
import scala.util.control._

class TypeInfo(var typeOK: Boolean, var identifier_type: String)

object typeCheckerTL {

  case class typeCheckerException(message: String) extends Exception(message)

  var writerAST: PrintWriter = null
  var nodeNumber: Int = 0

  var DOTstatements = ArrayBuffer[String]()

  def initializeAST() {
    nodeNumber = 0
  }

  def setColor(color: String, nodeId: String, DOTgraphInstructions: ArrayBuffer[String]) {

    //must escape '['  in a regex expression, because it starts a character class definition
    val searchFor = nodeId + " \\[label="
    val pattern = searchFor.r

    val loop = new Breaks;

    loop.breakable {

      for (i <- 1 to (DOTgraphInstructions.length - 1)) {
        if ((pattern findFirstIn DOTgraphInstructions(i)) != None) {
          //replace instruction with color
          //var replacement = DOTgraphInstructions(i).replaceFirst("white", color)
          var replacement = DOTgraphInstructions(i).replaceFirst("/x11/[a-z]*", "/x11/" + color)
          DOTgraphInstructions(i) = replacement
          loop.break
        } // end if

      } //end for

    } // end loop breakable

  } // end setColor

  def nextNode(): String = {
    nodeNumber = 1 + nodeNumber
    return "n" + nodeNumber
  }

  def setFileName(fileName: String) {
    writerAST = new PrintWriter(new File(fileName))
  }

  def addGraphNode(childLabel: String, parentNode: String, color: String): String = {
    //TODO UPDATE
    val newChildNode = nextNode()
    DOTstatements += newChildNode + " [label=\"" + childLabel + "\",fillcolor=\"/x11/" + color + "\",shape=box]" + "\n"
    DOTstatements += parentNode + " -> " + newChildNode + "\n"
    return newChildNode
  }

  def typeChecker(node: ASTnode, pNode: String): TypeInfo = {

    //initially set to (false, N/A)
    var validate = new TypeInfo(false, "N/A")

    node match {

      //<program> ::= PROGRAM <declarations> BEGIN <statementSequence> END
      case programASTnode(_, declsList, stmtList) => {
        //initialize globals
        DOTstatements = ArrayBuffer[String]()

        // DOT GRAPH PREAMBLE
        DOTstatements += "digraph parseTree {" + "\n"
        DOTstatements += "ordering=out;" + "\n"
        DOTstatements += "node [shape = box, style = filled];" + "\n"
        DOTstatements += pNode + " [label=\"<program>\",fillcolor=\"/x11/white\",shape=box]" + "\n"

        val validateDecls = typeChecker(declsList, pNode)
        val validateStmtSeq = typeChecker(stmtList, pNode)

        if (!validateDecls.typeOK || !validateStmtSeq.typeOK) {
          setColor("red", pNode, DOTstatements)
        } else {
          setColor("gray", pNode, DOTstatements)
        }

        DOTstatements += "}"

        //write ArrayBuffer out to DOT file
        for (statement <- DOTstatements) {
          writerAST.write(statement)
        }

        writerAST.flush()
        writerAST.close()

      } // end case programASTnode

      //<declarations> ::= VAR ident AS <type> SC <declarations> | ε
      case declarationsListASTnode(_, declaration, declarationList) => {
        val declarationDOTnode = addGraphNode("decl list", pNode, "white")
        val validateDeclaration = typeChecker(declaration, declarationDOTnode)

        // if there are no more declarations, no need to type check...
        if (!declarationList.isInstanceOf[AST_epsilon]) {
          val validateDecls = typeChecker(declarationList, declarationDOTnode)
        }

        // return true for typeOK as decl node traversals have completed
        validate.typeOK = true
      }
      case declartionASTnode(label, ident, type_) => {
        val identDOTnode = addGraphNode(label, pNode, "white")
        val validateType = typeChecker(type_, identDOTnode)

        // set color accordingly for decl node
        if (validateType.identifier_type == "INT") {
          setColor("green", identDOTnode, DOTstatements)
        } else if (validateType.identifier_type == "BOOL") {
          setColor("lightblue", identDOTnode, DOTstatements)
        }


        validate.identifier_type = validateType.identifier_type
        validate.typeOK = true

      }
      //<statementSequence> ::= <statement> SC <statementSequence> | ε
      case statementListASTnode(_, statement, statementList) => {

        var statementSequenceDOTnode: String = null

        if (!statementList.isInstanceOf[AST_epsilon]) {

          statementSequenceDOTnode = addGraphNode("Statement List", pNode, "white")

          val validateStmt = typeChecker(statement, statementSequenceDOTnode)
          val validateSeq = typeChecker(statementList, statementSequenceDOTnode)
          if (validateStmt.typeOK == true && validateSeq.typeOK == true) {
            validate.typeOK = true
            // this node has neutral color no matter the outcome
            setColor("white", statementSequenceDOTnode, DOTstatements)
          }

          else {
            // this node has neutral color no matter the outcome
            setColor("white", statementSequenceDOTnode, DOTstatements)
            validate.typeOK = false
          }
        }
        else {

          val validateStmt = typeChecker(statement, pNode)

          if (!validateStmt.typeOK) {
            validate.typeOK = false
            setColor("red", statementSequenceDOTnode, DOTstatements)
          } else {
            validate.typeOK = true
            setColor("green", statementSequenceDOTnode, DOTstatements)
          }
        }
      } // end case statementSequence
      //<ifStatement> ::= IF <expression> THEN <statementSequence> <elseClause> END
      case IfStatementASTnode(_, expression, statementList, elseClause) => {
        val IF_DOTnode = addGraphNode("<IF>", pNode, "white")
        val validateExpr = typeChecker(expression, IF_DOTnode)
        val validateStmtList = typeChecker(statementList, IF_DOTnode)
        val validateElse = typeChecker(elseClause, IF_DOTnode)

        if (validateExpr.typeOK == true &&
          validateStmtList.typeOK == true &&
          validateElse.typeOK == true) {
          validate.typeOK = true
          setColor("green", IF_DOTnode, DOTstatements)
        }
        else {
          setColor("red", IF_DOTnode, DOTstatements)
          validate.typeOK = false
        }
      }
      //<elseClause> ::= ELSE <statementSequence> | ε
      case ElseClauseStatementASTnode(_, statementList) => {
        val ElseClause_DOTnode = addGraphNode("<ELSE>", pNode, "white")
        val validateStmtList = typeChecker(statementList, ElseClause_DOTnode)

        if (validateStmtList.typeOK == false)
          setColor("red", ElseClause_DOTnode, DOTstatements)

        // pass typeOK back up the tree
        validate.typeOK = validateStmtList.typeOK
      }
      //<whileStatement> ::= WHILE <expression> DO <statementSequence> END
      case WhileStatementASTnode(_, expression, statementList) => {
        val WHILE_DOTnode = addGraphNode("<WHILE>", pNode, "grey")

        val validateExpr = typeChecker(expression, WHILE_DOTnode)
        val validateStmtList = typeChecker(statementList, WHILE_DOTnode)

        if (validateExpr.typeOK == true && validateStmtList.typeOK == true)
          validate.typeOK = true
        else {
          setColor("red", WHILE_DOTnode, DOTstatements)
          validate.typeOK = false
        }

      }
      //<writeInt> ::= WRITEINT <expression>
      case WRITEINT_ASTnode(_, expression) => {
        val writeint_DOTnode = addGraphNode("WRITEINT", pNode, "white")
        val validateExpr = typeChecker(expression, writeint_DOTnode)

        if (validateExpr.typeOK == true && validateExpr.identifier_type == "INT") {
          setColor("gray", writeint_DOTnode, DOTstatements)
          validate.typeOK = true
        }
        else {
          setColor("red", writeint_DOTnode, DOTstatements)
          println("TYPE ERROR - WRITEINT : " + node.toString())
          validate.typeOK = false
        }
      }
      //<assignment> ::= ident ASGN <assignType>
      case assignmentASTnode(label, ident, expr) => {

        val assignmentDOT_ASTnode = addGraphNode(label, pNode, "green")

        val validateIdent = typeChecker(ident, assignmentDOT_ASTnode)

        // check for Epsilon for READINT case
        val validateAsgnExpr = typeChecker(expr, assignmentDOT_ASTnode)

        if (validateAsgnExpr.identifier_type == "N/A") // expression is empty
          if (validateIdent.identifier_type == "INT") {
            // must be a ":= READINT" assignment
            setColor("gray", assignmentDOT_ASTnode, DOTstatements)
            validate.typeOK = true
          }
          else {
            setColor("red", assignmentDOT_ASTnode, DOTstatements)
            println("TYPE ERROR -  := READINT : " + node.toString())
            validate.typeOK = false
          }
        else if ((validateIdent.identifier_type == validateAsgnExpr.identifier_type) && (validateAsgnExpr.typeOK == true)) {
          //BOOL or INT
          setColor("gray", assignmentDOT_ASTnode, DOTstatements)
          validate.typeOK = true
        }
        else {
          setColor("red", assignmentDOT_ASTnode, DOTstatements)
          println("TYPE ERROR - ASSIGNMENT : " + node.toString())
          validate.typeOK = false

        }

      }
      //<multiplicativeExpr> ::= MULTIPLICATIVE <factor> <multiplicativeExpr> | ε
      case multiplicativeExprASTnode(_, operator, leftExpr, rightExpr) => {

        val multiplicativeExprASTnode = addGraphNode(operator, pNode, "green")

        val validateLeft = typeChecker(leftExpr, multiplicativeExprASTnode)
        val validateRight = typeChecker(rightExpr, multiplicativeExprASTnode)

        if (validateLeft.identifier_type == "INT" && (validateRight.identifier_type == "INT")) {
          setColor("green", multiplicativeExprASTnode, DOTstatements)
          validate.typeOK = true
          validate.identifier_type = "INT"
        }
        else {
          setColor("red", multiplicativeExprASTnode, DOTstatements)
          println("TYPE ERROR - MULTIPLICATIVE '" + operator + "': " + node.toString())
          validate.typeOK = false
        }

      }
      //<compareExpr> ::= COMPARE <simpleExpression> <compareExpr> | ε
      case compareExprASTnode(_, operator, leftExpr, rightExpr) => {

        val compareExprASTnode = addGraphNode(operator, pNode, "lightblue")

        val validateLeft = typeChecker(leftExpr, compareExprASTnode)
        val validateRight = typeChecker(rightExpr, compareExprASTnode)

        if (validateLeft.identifier_type == "INT" && validateRight.identifier_type == "INT") {
          validate.typeOK = true
          validate.identifier_type = "BOOL"
        }
        else {
          setColor("red", compareExprASTnode, DOTstatements)
          println("TYPE ERROR - COMPARE '" + operator + "': " + node.toString())
          validate.typeOK = false
        }
      }
      //<additiveExpr> ::= ADDITIVE <term> <additiveExpr> | ε
      case additiveExprASTnode(_, operator, leftExpr, rightExpr) => {

        val additiveExprASTnode = addGraphNode(operator, pNode, "green")

        val validateLeft = typeChecker(leftExpr, additiveExprASTnode)
        val validateRight = typeChecker(rightExpr, additiveExprASTnode)

        if (validateLeft.identifier_type == "INT" && (validateRight.identifier_type == "INT")) {
          validate.typeOK = true
          validate.identifier_type = "INT"
        }
        else {
          setColor("red", additiveExprASTnode, DOTstatements)
          println("TYPE ERROR - ADDITIVE '" + operator + "': " + node.toString())
          validate.typeOK = false
        }
      }
      case identASTnode(label, value) => {
        // Get identified type  from symbol table
        val identType = ParserTL.symbolTable(value)

        if (identType == "BOOL")
          addGraphNode(label, pNode, "lightblue") //BOOL type
        else
          addGraphNode(label, pNode, "green") //INT type

        validate.typeOK = true
        validate.identifier_type = identType
      }
      case numASTnode(_, value) => {
        addGraphNode(value, pNode, "green")
        validate.typeOK = true
        validate.identifier_type = "INT"
      }
      //<factor> ::= boollit
      case boollitASTnode(_, value) => {
        addGraphNode(value, pNode, "lightblue")
        validate.typeOK = true
        validate.identifier_type = "BOOL"
      }
      case AST_epsilon() => {
        // return true for typeOK, as this is epsilon and the null case
        validate.typeOK = true
      }
      case _ => {
        var msg: String = "";
        if (node != null) {
          msg = node.toString()
          throw new typeCheckerException("UNKNOWN AST NODE TYPE " + "\n" + msg + "\n")
        }
        else {
          throw new typeCheckerException("TEST NODE IS NULL " + msg + "\n")
        }
      } // end case _

    } // end match

    return validate

  } // end typeChecker

  def main(argv: Array[String]) {

    //START BUILDING UP THIS TEST AST TREE FROM THE SIMPLE PROGRAM BELOW
    //  program
    //    var X as int ;
    //  begin
    //    X := 5
    //  end

    val source = "X := 5"

    val ident = identASTnode("source string", "X")
    val num = numASTnode("source string", "5")
    val identNode = declartionASTnode("source string", ident, num)
    //    val multiplicative_expr : multiplicativeExprASTnode  =  multiplicativeExprASTnode(source, MUL, factor_,  AST_epsilon())
    //    val addExpr : additiveExprASTnode = additiveExprASTnode(source, ADD, term_,  AST_epsilon())
    //    val compare_expr : compareExprASTnode = compareExprASTnode(source, COMP, simple_expr,  AST_epsilon())
    val assign = assignmentASTnode(":=", ident, num)
    val stmtSeq: statementListASTnode = statementListASTnode(source, assign, AST_epsilon())
    val decls = declarationsListASTnode(source, identNode, AST_epsilon())
    val prog = programASTnode(source, decls, stmtSeq)



    // the DOT graph node
    val progGraphNode: String = nextNode()

    //TEST HERE FIRST
    typeChecker(prog, progGraphNode)

  }

}

// end object typeCheckerTL