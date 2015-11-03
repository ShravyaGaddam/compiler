/*
[ * ParserTL.scala
 * CS5363-E
 * Spring 2015
 * Amulya Battu tester
 * Gabe Fernandez design, developer
 * Shravya Gaddam tester
 * David Holland design, developer
 */
package parser

import java.io._

import scanner._

import scala.io.Source

object ParserTL {

  //token case class definitions
  sealed abstract class Token

  class KeyWord extends Token

  class Type extends Token

  class Operator extends Token

  case class MULTIPLICATIVE(value: String) extends Operator

  case class ADDITIVE(value: String) extends Operator

  case class COMPARE(value: String) extends Operator

  case class Num(value: Int) extends Token

  case class Boollit(value: String) extends Token

  case class Ident(value: String) extends Token

  case object INT extends Type

  case object BOOL extends Type

  case object PROGRAM extends KeyWord

  case object BEGIN extends KeyWord

  case object END extends KeyWord

  case object IF extends KeyWord

  case object THEN extends KeyWord

  case object ELSE extends KeyWord

  case object WHILE extends KeyWord

  case object DO extends KeyWord

  case object WRITEINT extends KeyWord

  case object READINT extends KeyWord

  case object VAR extends KeyWord

  case object AS extends KeyWord

  case object ASGN extends KeyWord

  case object SC extends KeyWord

  case object LP extends KeyWord

  case object RP extends KeyWord


  //each subclass has its own number and types of parameters!
  //NOTE: May not be able to have source line for now (look into it)

  //AST node case class definitions
  sealed abstract class ASTnode()

  case class ExprASTnode() extends ASTnode

  case class AST_epsilon() extends ASTnode

  //AST node that represents the ε condition in a production rule
  case class programASTnode(nodeLabel: String, declarations: ASTnode, statementSequence: ASTnode) extends ASTnode

  case class declarationsListASTnode(nodeLabel: String, declIdentNode: ASTnode, declarations: ASTnode) extends ASTnode

  case class declartionASTnode(nodeLabel: String, identNode: ASTnode, typeLeaf: ASTnode) extends ASTnode

  case class statementListASTnode(nodeLabel: String, statement: statement, var statementList: ASTnode) extends ASTnode

  class statement() extends ASTnode

  // AST node category
  case class IfStatementASTnode(nodeLabel: String, expression: ASTnode, statementSeq: ASTnode, elseClause: ASTnode) extends statement

  case class WhileStatementASTnode(nodeLabel: String, expression: ASTnode, statementSeq: ASTnode) extends statement

  case class ElseClauseStatementASTnode(nodeLabel: String, statementSeq: ASTnode) extends statement

  case class assignmentASTnode(nodeLabel: String, assignType: ASTnode, ident: ASTnode) extends statement

  case class WRITEINT_ASTnode(nodeLabel: String, expression: ASTnode) extends statement

  case class compareExprASTnode(nodeLabel: String, operator: String, leftExpr: ASTnode, rightExpr: ASTnode) extends ASTnode

  case class simpleExpressionASTnode(nodeLabel: String, term: ASTnode, AdditiveExpr: ASTnode) extends ASTnode

  case class additiveExprASTnode(nodeLabel: String, operator: String, leftExpr: ASTnode, rightExpr: ASTnode) extends ASTnode

  case class multiplicativeExprASTnode(val nodeLabel: String, val operator: String, val leftExpr: ASTnode, val rightExpr: ASTnode) extends ASTnode

  case class identASTnode(nodeLabel: String, val value: String) extends ASTnode

  case class numASTnode(nodeLabel: String, value: String) extends ASTnode

  case class boollitASTnode(nodeLabel: String, value: String) extends ASTnode

  //case class plusExpre(label : String, expr1 : expressionASTnode, expr2 : expressionASTnode) extends ASTnode
  //case class minusExpre(label : String, expr1 : expressionASTnode, expr2 : expressionASTnode) extends ASTnode
  //case class timesExpre(label : String, expr1 : expressionASTnode, expr2 : expressionASTnode) extends ASTnode

  // TypeChecker SymbolTable HashMap
  var symbolTable: Map[String, String] = Map()

  case class ParseException(message: String) extends Exception(message)

  case class ScannerException(message: String) extends Exception(message)

  case class DoneException(message: String) extends Exception(message)

  // throws ParseException which must be caught by caller
  //  def parser(tokens : List[Token], ptDotFile : String, AST_DotFile : String) : Unit = {
  def parser(tokens: List[Token], ptDotFile: String): ASTnode = {

    //initialize globals
    symbolTable = Map()
    var remaining = tokens
    val writer = new PrintWriter(new File(ptDotFile))
    var nodeNumber: Int = 0


    // BEGIN TL BNF PRODUCTION DEFINITIONS

    def nextNode(): String = {
      nodeNumber = 1 + nodeNumber
      return "n" + nodeNumber
    }

    def addGraphNode(childLabel: String, parentNode: String): String = {
      val newChildNode = nextNode()
      writer.write(newChildNode + " [label=\"" + childLabel + "\",fillcolor=\"/x11/white\",shape=box]" + "\n")
      writer.write(parentNode + " -> " + newChildNode + "\n")
      return newChildNode
    }

    // <program> ::= PROGRAM <declarations> BEGIN <statementSequence> END
    //  Δ <program>.ptr = makeSubtree("program", <declaration>.ptr, <statementSequence>.ptr)
    def program(): programASTnode = {

      //SPECIAL ONE TIME SET-UP for DOT file
      writer.write("digraph parseTree {" + "\n")
      writer.write("ordering=out;" + "\n")
      writer.write("node [shape = box, style = filled];" + "\n")
      val DOTnodeRoot: String = nextNode()
      writer.write(DOTnodeRoot + " [label=\"<program>\",fillcolor=\"/x11/white\",shape=box]" + "\n")

      // Attributes
      var program_ptr: ASTnode = null
      var multiplicativeExpr_st: ASTnode = null

      if (remaining.head != PROGRAM)
        throw new ParseException("<program> Expected PROGRAM, not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail
      val programDOTnode = addGraphNode(PROGRAM.toString(), DOTnodeRoot)

      val decls_root: declarationsListASTnode = null //IS THIS CORRECT ?????, starting with a empty declaration subtree
      val declarations_ptr = declarations(programDOTnode) // pass in parent Node, which is initially null

      if (remaining.head != BEGIN)
        throw new ParseException("<program> Expected BEGIN, not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail
      addGraphNode(BEGIN.toString(), programDOTnode)

      // ST is null for top of tree for AST Generation
      val statementSequence_ptr = statementSequence(programDOTnode)

      if (remaining.head != END)
        throw new ParseException("<program> Expected END, not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail
      addGraphNode(END.toString(), programDOTnode)
      writer.write("}")
      writer.flush()

      return programASTnode("program", declarations_ptr, statementSequence_ptr)

    } // end program()

    /*
      ORIGINAL   <declarations> ::= VAR ident AS <type> SC <declarations> | ε
      
      <declarations1> ::= VAR ident AS <type> SC <declarations2>
          Δ <declaration1>.ptr = makeASTnode("declarations", declIdentNode(ident.val, type.ptr), <declarations2>.ptr)
      <declarations> ::=  ε
          Δ <declaration>.ptr = <declaration>.st
     */
    def declarations(pNode: String): ASTnode = {

      var ident: identASTnode = null

      // Attributes
      var decls_ptr: ASTnode = null
      var decls2_ptr: ASTnode = null
      var type_ptr: ASTnode = null
      var identNode_ptr: ASTnode = null
      var identNodeVal: String = null
      var identKey: String = null

      remaining.headOption match {
        // case epsilon
        //FOLLOW(<declarations>) = {BEGIN}
        case Some(BEGIN) => {
          // print epsilon token in parse tree
          addGraphNode("&#949;", pNode)
          decls_ptr = AST_epsilon() //at the bottom, return the whole tree
        }
        case Some(VAR) => {
          val declGraphNode = addGraphNode("<declarations>", pNode)
          remaining = remaining.tail
          addGraphNode(VAR.toString(), declGraphNode)

          remaining.headOption match {
            case Some(Ident(_)) => {

              // Parse Tree
              addGraphNode("ident: " + remaining.head.asInstanceOf[Ident].value, declGraphNode)
              identNodeVal = remaining.head.asInstanceOf[Ident].value
              identNode_ptr = identASTnode("decl: " + remaining.head.asInstanceOf[Ident].value, remaining.head.asInstanceOf[Ident].value)

              identKey = identNodeVal

              remaining = remaining.tail

            }
            case _ => throw new ParseException("<declarations> Expected Ident, not: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())
          } // end inner match

          // next token must be AS
          if (remaining.head != AS)
            throw new ParseException("<declarations> Expected AS, not: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())

          addGraphNode(AS.toString(), declGraphNode)
          remaining = remaining.tail

          type_ptr = typeTL(declGraphNode)

          // check type and load into symbol table
          if (type_ptr.isInstanceOf[numASTnode]) {
            // create a hash map
            symbolTable += (identKey -> "INT")
          } else if (type_ptr.isInstanceOf[boollitASTnode]) {
            symbolTable += (identKey -> "BOOL")
          } else {
            // throw error
            throw new typeCheckerTL.typeCheckerException("<declarations> TypeChecker Error, not: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())
          }

          // create declIdentASTnode
          val declIdentnode = declartionASTnode("decl: " + identNodeVal, identNode_ptr, type_ptr)

          //next token must be SC
          if (remaining.head != SC)
            throw new ParseException("<declarations> Expected SC, not: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())

          addGraphNode(";", declGraphNode)
          remaining = remaining.tail

          // decls2_st is a reference to the subtree built in this recursive call for the next 
          // TODO: Confirm that decls1_st is correct for AST

          decls2_ptr = declarations(declGraphNode) //coming back up recursive stack with the full tree pushed back up
          decls_ptr = declarationsListASTnode("decl list", declIdentnode, decls2_ptr)


        }
        case _ => throw new ParseException("<declarations> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())

      } // end match

      return decls_ptr;
    } // end declarations()


    /*
     <type> ::= INT
        Δ type.ptr = leaf(INT.value)
     <type> ::= BOOL
        Δ type.ptr = leaf(BOOL.value)
     */
    def typeTL(pNode: String): ASTnode = {
      val typeNode = addGraphNode("<type>", pNode)
      var type_ptr: ASTnode = null

      remaining.headOption match {
        case Some(INT) => {
          addGraphNode(remaining.head.toString(), typeNode)
          // Set AST node accordingly
          type_ptr = numASTnode("int", remaining.head.toString()) // TODO: Double check second param          
          remaining = remaining.tail
        }
        case Some(BOOL) => {
          addGraphNode(remaining.head.toString(), typeNode)
          // Set AST node accordingly
          type_ptr = boollitASTnode("bool", remaining.head.toString()) // TODO: Double check second param
          remaining = remaining.tail
        }
        case _ => throw new ParseException("<type> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }

      return type_ptr
    } // end typeTL()


    /*
    ORIGINAL   <statementSequence> ::= <statement> SC <statementSequence> | ε
    
    <statementSequence1> ::= <statement> SC <statementSequence2>
      Δ <statementSequence1>.ptr = makeASTnode("statementSequence", <statement>.ptr, <statementSequence2>.ptr)
    <statementSequence> ::=  ε
      Δ <statementSequence>.ptr = nil  //at the terminal condition, no more recursion, begin build AST going back up to the root
     */
    def statementSequence(pNode: String): ASTnode = {

      // Attributes
      var statementSequence2_ptr: ASTnode = null
      var statementSequence1_ptr: ASTnode = null

      remaining.headOption match {
        // case <statement>
        //FIRST+(<statement>) = {Ident, IF, WHILE, WRITEINT} because <statement> can never go to epsilon
        case (Some(Ident(_)) | Some(IF) | Some(WHILE) | Some(WRITEINT)) => {

          var stmtType = remaining.head.toString();

          val statementSequenceNode = addGraphNode("<statementSequence>", pNode)

          var stmt_ptr = statement(statementSequenceNode)

          if (remaining.head != SC) {
            throw new ParseException("<statementSequence> Expected SC, not: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())
          }

          addGraphNode(";", statementSequenceNode)
          remaining = remaining.tail

          // TODO: Why does statementSequence2_ptr become null?
          statementSequence2_ptr = statementSequence(statementSequenceNode)
          statementSequence1_ptr = statementListASTnode("stmt list", stmt_ptr, statementSequence2_ptr)
        }
        // case epsilon
        //FOLLOW(<statementSequence>) = {END, ELSE}
        case (Some(END) | Some(ELSE)) => {
          // PARSE TREE
          addGraphNode("&#949;", pNode)

          // empty AST node
          //statementSequence1_ptr = null
          statementSequence1_ptr = AST_epsilon()
        }
        case _ => throw new ParseException("<statementSequence> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      } // end match

      //AST node
      return statementSequence1_ptr
    }

    /*
     //build the AST from bottom-up, no '.st' parameter in the statement() def
     <statement> ::= <assignment>
       Δ <statement>.ptr = <assignment>.ptr
     <statement> ::= <ifStatement>
       Δ <statement>.ptr = <ifStatement>.ptr
     <statement> ::= <whileStatement>
       Δ <statement>.ptr = <whileStatement>.ptr
     <statement> ::= <writeInt>
       Δ <statement>.ptr = <writeInt>.ptr
      */
    def statement(pNode: String): statement = {
      val statementDOTnode = addGraphNode("<statement>", pNode)
      var stmt_ptr: statement = null

      remaining.headOption match {

        case Some(Ident(_)) => {
          stmt_ptr = assignment(statementDOTnode)
        }

        case Some(IF) => {
          stmt_ptr = ifStatement(statementDOTnode)
        }

        case Some(WHILE) => {
          stmt_ptr = whileStatement(statementDOTnode)
        }

        case Some(WRITEINT) => {
          stmt_ptr = writeInt(statementDOTnode)
        }

        case _ => throw new ParseException("<statement> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }

      return stmt_ptr
    }

    /*
       ORIGINAL  <assignment> ::= ident ASGN <expression> | ident ASGN READINT 
       
      <assignment> ::= ident ASGN <assignType>
           Δ <assignment>.ptr =  makeASTnode("assignment", leaf(ident.val), leaf(ASGN.val), <assignmentType>.ptr)
      <assignType> ::= READINT | <expression>
           Δ <assignmentType>.ptr = leaf(READINT.val)
           Δ <assignmentType>.ptr = <expression>.ptr
     */
    // TODO: Do we need to create an assignment node, even though it will not be in the AST TREE?
    def assignment(pNode: String): statement = {
      val assignmentNode = addGraphNode("<assignment>", pNode)
      var asgn_ptr: statement = null
      var asgnType_ptr: ASTnode = null
      var ident_leaf: ASTnode = null

      remaining.headOption match {
        case Some(Ident(_)) => {
          addGraphNode("ident: " + remaining.head.asInstanceOf[Ident].value, assignmentNode)
          ident_leaf = identASTnode(remaining.head.asInstanceOf[Ident].value, remaining.head.asInstanceOf[Ident].value)
          remaining = remaining.tail

          if (remaining.head != ASGN)
            throw new ParseException("<assignment> Expected ASGN,  remaining.head: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())
          addGraphNode(":=", assignmentNode)
          remaining = remaining.tail

          asgnType_ptr = assignType(assignmentNode)

          //if(asgnType_ptr.isInstanceOf[READINT_AST])
          if (asgnType_ptr.isInstanceOf[AST_epsilon])
            asgn_ptr = assignmentASTnode(":= READINT", ident_leaf, AST_epsilon()) //empty expression
          else
          // create assignmentASTnode
            asgn_ptr = assignmentASTnode(":=", ident_leaf, asgnType_ptr)

        }
        case _ => throw new ParseException("<assignment> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }
      return asgn_ptr
    }

    /*
    <assignType> ::= READINT | <expression>
      Δ <assignmentType>.ptr = leaf(READINT.val)
      Δ <assignmentType>.ptr = <expression>.ptr
     */
    // TODO: Review assignType, specifically FIRST+(<expression>). 
    // Do we need to do anything with asgn_ptr there?
    def assignType(pNode: String): ASTnode = {
      val assignTypeNode = addGraphNode("<assignType>", pNode)
      var asgn_ptr: ASTnode = null

      remaining.headOption match {
        case Some(READINT) => {
          addGraphNode(READINT.toString(), assignTypeNode)

          //asgn_ptr = READINT_AST(":= READINT", ": = " + READINT.toString())
          asgn_ptr = AST_epsilon() //case of empty expression, only the READINT operator
          remaining = remaining.tail
        }

        // case (<expression>)
        // FIRST+(<expression>) = {LP,Ident, Boollit, Num} because <expression> CANNOT go to epsilon
        case (Some(LP) |
              Some(Ident(_)) |
              Some(Boollit(_)) |
              Some(Num(_))
          ) => asgn_ptr = expression(assignTypeNode)
        case _ => throw new ParseException("<assignType> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }

      return asgn_ptr
    }

    /* 
     <ifStatement> ::= IF <expression> THEN <statementSequence> <elseClause> END
        Δ <ifStatement>.ptr = makeASTnode("if", <expresssion>.ptr, <statementSequence.ptr>, <elseClause>.ptr)
     */
    def ifStatement(pNode: String): statement = {
      val ifStatementDOTnode = addGraphNode("<ifStatement>", pNode)
      var ifStmt_ptr: statement = null

      if (remaining.head != IF)
        throw new ParseException("<ifStatement> Expected IF,  remaining.head: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())

      remaining = remaining.tail

      var expr_ptr = expression(ifStatementDOTnode)

      if (remaining.head != THEN)
        throw new ParseException("<ifStatement> Expected THEN,  remaining.head: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail

      var stmtSeq_ptr = statementSequence(ifStatementDOTnode)

      var elseCls_ptr = elseClause(ifStatementDOTnode)

      if (remaining.head != END)
        throw new ParseException("<ifStatement> Expected END,  remaining.head: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail

      // AST NODE
      ifStmt_ptr = IfStatementASTnode("sourceLine", expr_ptr, stmtSeq_ptr, elseCls_ptr)
      return ifStmt_ptr
    }

    /*
     <elseClause> ::= ELSE <statementSequence> 
          Δ <elseClause>.ptr = makeASTnode("else", <statementSequence>.st)
     <elseClause> ::=  ε
          Δ <elseClause>.ptr = Nil.st
     */
    def elseClause(pNode: String): ASTnode = {
      val elseNode = addGraphNode("<elseStatement>", pNode)
      var else_ptr: ASTnode = null
      var stmtSeq_ptr: ASTnode = null

      remaining.headOption match {
        case Some(ELSE) => {
          remaining = remaining.tail

          stmtSeq_ptr = statementSequence(elseNode)
          else_ptr = ElseClauseStatementASTnode("sourceLine", stmtSeq_ptr)
        }
        // case epsilon
        //FOLLOW(<elseClause>) = {END}
        case Some(END) => {
          addGraphNode("&#949;", elseNode)
          else_ptr = AST_epsilon()
        }
        case _ => throw new ParseException("<elseClause> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      } // end match


      return else_ptr
    } // end elseClause


    /*
     <whileStatement> ::= WHILE <expression> DO <statementSequence> END
         Δ <whileStatement>.ptr = makeASTnode("while", <expression>.ptr, <statementSequence>.ptr)
    */
    def whileStatement(pNode: String): statement = {
      var whileStatementNode = addGraphNode("<whileStatement>", pNode)
      var while_ptr: statement = null
      var expr_ptr: ASTnode = null
      var stmtSeq_ptr: ASTnode = null

      if (remaining.head != WHILE)
        throw new ParseException("<whileStatement> Expected WHILE, not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail

      // Print While Keyword
      addGraphNode("WHILE", whileStatementNode)

      expr_ptr = expression(whileStatementNode)

      if (remaining.head != DO)
        throw new ParseException("<whileStatement> Expected DO,  not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail

      // Print DO Keyword
      addGraphNode("DO", whileStatementNode)

      stmtSeq_ptr = statementSequence(whileStatementNode)

      if (remaining.head != END)
        throw new ParseException("<whileStatement> Expected END,  not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      remaining = remaining.tail

      // Print END Keyword
      addGraphNode("END", whileStatementNode)

      while_ptr = WhileStatementASTnode("sourceLine", expr_ptr, stmtSeq_ptr)
      return while_ptr
    } // end whileStatement

    /*
     <writeInt> ::= WRITEINT <expression>
        Δ <writeInt>.ptr = makeASTnode("writeInt", <expression>.ptr)
    */
    // TODO: FIX THIS UP -- EXPRESSION PTR IS NULL!!!
    def writeInt(pNode: String): statement = {
      val writeIntDOTnode = addGraphNode("<writeInt>", pNode)
      var writeInt_ptr: statement = null
      var expression_ptr: ASTnode = null

      if (remaining.head != WRITEINT)
        throw new ParseException("<writeInt> Expected WRITEINT, not: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      addGraphNode(remaining.head.toString(), writeIntDOTnode)
      remaining = remaining.tail

      expression_ptr = expression(writeIntDOTnode)
      writeInt_ptr = WRITEINT_ASTnode("writeInt", expression_ptr)
      return writeInt_ptr

    } // end writeInt

    // ORIGINAL <expression> ::= <simpleExpression> | <simpleExpression> COMPARE <expression>
    // REFACTORED AND ATTRIBUTED
    //<expression> ::= <simpleExpression> <compareExpr>
    //   Δ <compareExpr>.st = <simpleExpression>.ptr
    //   Δ <expression.ptr = <compareExpr>.ptr
    //COMPARE IS NOT ASSOCIATIVE. IT IS A BINARY OPERATOR THAT RETURNS A BOOLEAN, 
    //    4 < 5 < 6 will be caught by TYPE CHECKER
    //parser currently parses "5 < 5 < 4 + 2", which is NONSENSICAL
    def expression(pNode: String): ASTnode = {
      val expressionNode = addGraphNode("<expression>", pNode)

      // Attributes
      var compareExpr_st: ASTnode = null
      var expression_ptr: ASTnode = null

      remaining.headOption match {
        // case (<simpleExpression>)
        // FIRST+(<expression> -> <simpleExpression> <compareExpr>) = FIIRST(<simpleExpression>)is {LP,Ident, Boollit, Num}
        //because <simpleExpression>  cannot go to ε
        case (Some(LP) | Some(Ident(_)) |
              Some(Boollit(_)) |
              Some(Num(_))
          ) => {

          compareExpr_st = simpleExpression(expressionNode)

          // if compareExpr returns EPSILON,
          expression_ptr = compareExpr(expressionNode, compareExpr_st)

          if (expression_ptr.isInstanceOf[AST_epsilon]) {
            // There is no compare operator
            expression_ptr = compareExpr_st
          }

        }
        case _ => throw new ParseException("<expression> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }
      return expression_ptr
    } // end expression

    /*
     ORIGINAL  <compareExpr1> ::= COMPARE <simpleExpression> <compareExpr2>
        //finally the INHERITED ATTRIB
        Δ  <compareExpr2>.st = makeASTnode("compareExpr", leaf(COMPARE.val), <compareExpr1>.st, <simpleExpression>.ptr)
        //SYNTH ATTRIB ON THE WAY BACK TO ROOT, PASSING THE SUBTREE BACK TO THe PARENT
        Δ  <compareExpr1>.ptr = <compareExpr2>.ptr
    <compareExpr> ::=  ε
        Δ  <compareExpr>.ptr = <compareExpr>.st 
       // Δ  <compareExpr>.ptr = Nil.st    
    */
    def compareExpr(pNode: String, compareExpr1_st: ASTnode): ASTnode = {

      // Attributes
      var compareExpr1_ptr: ASTnode = null
      var compareExpr2_st: ASTnode = null

      remaining.headOption match {
        // check for EPSILON
        case (Some(IF) | Some(THEN) | Some(DO) | Some(SC) | Some(MULTIPLICATIVE(_)) | Some(ADDITIVE(_))) => {
          // EPSILON CASE found
          // set attribute PTR to ST
          // We have reached the bottom of the tree.
          // We are copying the inherited subtree to the synthesized ptr to return back up the tree
          // addGraphNode("&#949;", pNode)  //epsilon node
          //compareExpr1_ptr = AST_epsilon()
          compareExpr1_ptr = compareExpr1_st
        }
        //recursive case 
        case Some(COMPARE(_)) => {

          // We found COMPARE, this is not EPSILON
          val compareExprNode = addGraphNode("<compareExpr>", pNode)

          // We are  traversing down the tree with inherited attributes

          val compareOP = remaining.head.asInstanceOf[COMPARE].value

          addGraphNode(remaining.head.asInstanceOf[COMPARE].value, compareExprNode)
          remaining = remaining.tail //remove operator token

          val simpleExpression_ptr = simpleExpression(compareExprNode)

          //set  SYNTHESIZED attribute
          compareExpr2_st = compareExprASTnode("sourceString", compareOP, compareExpr1_st, simpleExpression_ptr)

          //set  SYNTHESIZED attribute  and recurse
          compareExpr1_ptr = compareExpr(compareExprNode, compareExpr2_st)

        }
        case _ => throw new ParseException("<additiveExpr> at TOKEN: " + remaining.head.toString() + "\nremaining tokens: " + remaining.toString())
      } // end match
      return compareExpr1_ptr
    } // end compareExpr

    /*
    ORIGINAL <simpleExpression> ::= <term> <additiveExp>
       Δ <additiveExpr>.st = <term>.ptr
       Δ <simpleExpression>.ptr = <additiveExpr>.ptr
    */
    def simpleExpression(pNode: String): ASTnode = {
      val simpleExpressionNode = addGraphNode("<simpleExpression>", pNode)

      // Attributes
      var additiveExpr_st: ASTnode = null
      var simpleExpression_ptr: ASTnode = null

      remaining.headOption match {
        // case (<term>)
        // FIRST+(<term>) = {LP,Ident, Boollit, Num} = FIRST(<term>), because <term> cannot go to epsilon
        case (Some(LP) | Some(Ident(_)) |
              Some(Boollit(_)) |
              Some(Num(_))
          ) => {

          additiveExpr_st = term(simpleExpressionNode)

          simpleExpression_ptr = additiveExpr(simpleExpressionNode, additiveExpr_st)

          //TODO.  NO AST NODE CREATED???????  CHECK THE ATTRIBUTED GRAMMAR
          //simpleExpression_ptr = simpleExpressionASTnode("sourceLine", term_ptr, additiveExpr_ptr)

        }
        case _ => throw new ParseException("<simpleExpression> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }
      return simpleExpression_ptr
    } // end SimpleExpression

    /* 
    ORIGINAL    <additiveExpr> ::= ADDITIVE <term> <additiveExpr> | ε
    ATTRIBUTED
    <additiveExpr1> ::= ADDITIVE <term> <additiveExpr2>
    finally the INHERITED ATTRIB
       Δ  <additiveExpr2>.st = makeASTnode("additiveExpr", <additiveExpr1>.st, leaf(ADDITIVE.val), <term>.ptr)
    SYNTH ATTRIB ON THE WAY BACK TO ROOT, PASSING THE SUBTREE BACK TO THe PARENT
        Δ  <additiveExpr1>.ptr = <additiveExpr2>.ptr
	  <additiveExpr> ::=  ε
        Δ  <additiveExpr>.ptr = <additiveExpr>.st    
    */
    def additiveExpr(pNode: String, additiveExpr1_st: ASTnode): ASTnode = {

      // Attributes
      var additiveExpr1_ptr: ASTnode = null
      var additiveExpr2_st: ASTnode = null

      remaining.headOption match {
        // check for EPSILON
        case (Some(IF) | Some(THEN) | Some(DO) | Some(SC) | Some(MULTIPLICATIVE(_)) | Some(COMPARE(_))) => {
          // EPSILON CASE found
          // set attribute PTR to ST
          // We have reached the bottom of the tree.
          // We are copying the inherited subtree to the synthesized ptr to return back up the tree
          //addGraphNode("&#949;", pNode)  //epsilon node
          //additiveExpr1_ptr =  AST_epsilon()
          additiveExpr1_ptr = additiveExpr1_st
        }
        //recursive case 
        case Some(ADDITIVE(_)) => {

          // We found ADDITIVE, so it's  not EPSILON
          val additiveExprNode = addGraphNode("<additiveExpr>", pNode)

          // We are  traversing down the tree with inherited attributes

          val additiveOP = remaining.head.asInstanceOf[ADDITIVE].value

          addGraphNode(remaining.head.asInstanceOf[ADDITIVE].value, additiveExprNode)
          remaining = remaining.tail //remove operator token

          val term_ptr = term(additiveExprNode)


          //set  SYNTHESIZED attribute
          additiveExpr2_st = additiveExprASTnode("sourceString", additiveOP, additiveExpr1_st, term_ptr)

          //set  SYNTHESIZED attribute  and recurse
          additiveExpr1_ptr = additiveExpr(additiveExprNode, additiveExpr2_st)

        }
        case _ => throw new ParseException("<additiveExpr> at TOKEN: " + remaining.head.toString() + "\nremaining tokens: " + remaining.toString())
      } // end match

      return additiveExpr1_ptr //SYNTHESIZED ATTRIIBUTE
    } // end additiveExpr

    /*
    <term> ::= <factor> <multiplicativeExpr>
      Δ <multiplicativeExpr>.st = <factor>.ptr
      Δ <term>.ptr = <multiplicativeExpr>.ptr
    */
    def term(pNode: String): ASTnode = {
      val termNode = addGraphNode("<term>", pNode)

      // Attributes
      var term_ptr: ASTnode = null
      var multiplicativeExpr_st: ASTnode = null

      remaining.headOption match {
        // case (<factor>)
        // FIRST+(<factor>) = {LP,Ident, Boollit, Num}
        case (Some(LP) | Some(Ident(_)) |
              Some(Boollit(_)) |
              Some(Num(_))
          ) => {

          val multiplicativeExpr_st = factor(termNode)

          val multiplicativeExpr_ptr = multiplicativeExpr(termNode, multiplicativeExpr_st)

          //TODO.  NO AST NODE CREATED???????  CHECK THE ATTRIBUTED GRAMMAR
          // term_ptr = termASTnode("sourceLine", factor_ptr, multiplicativeExpr_ptr)

          term_ptr = multiplicativeExpr_ptr

        }
        case _ => throw new ParseException("<term> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }
      return term_ptr //pass back SYNTHESIZED attribute
    }

    /*
    ORIGINAL <multiplicativeExpr> ::= MULTIPLICATIVE <factor> <multiplicativeExpr>  | ε
    ATTRIBUTED
    <multiplicativeExpr1> ::= MULTIPLICATIVE <factor> <multiplicativeExpr2>
      Δ  <multiplicativeExpr2>.st = makeASTnode("multiplicativeExpr", leaf(MULTIPLICATIVE.val),  <factor>.ptr, <multiplicativeExpr1>.st)                                    
    SYNTH ATTRIB ON THE WAY BACK TO ROOT, PASSING THE SUBTREE BACK TO THE PARENT
      Δ  <multiplicativeExpr1>.ptr = <multiplicativeExpr2>.ptr
    <multiplicativeExpr1> ::=  ε
      Δ  <multiplicativeExpr1.ptr = <multiplicativeExpr1>.st   
    */
    def multiplicativeExpr(pNode: String, multiplicativeExpr1_st: ASTnode): ASTnode = {

      // Attributes
      var multiplicativeExpr1_ptr: ASTnode = null
      var multiplicativeExpr2_st: ASTnode = null

      remaining.headOption match {

        // check for EPSILON
        case (Some(IF) | Some(THEN) | Some(DO) | Some(SC) | Some(ADDITIVE(_)) | Some(COMPARE(_))) => {
          // EPSILON CASE found
          // set attribute PTR to ST
          // We have reached the bottom of the tree.
          // We are copying the inherited subtree to the synthesized ptr to return back up the tree
          //addGraphNode("&#949;", pNode)  //epsilon node
          //multiplicativeExpr1_ptr = AST_epsilon()
          multiplicativeExpr1_ptr = multiplicativeExpr1_st
        }
        //recursive case
        case Some(MULTIPLICATIVE(_)) => {
          // We found MULTIPLICATIVE, this is not EPSILON
          val multiplicativeExprNode = addGraphNode("<multiplicativeExpr>", pNode)

          // We are  traversing down the tree with inherited attributes

          val multiplicativeOP = remaining.head.asInstanceOf[MULTIPLICATIVE].value

          addGraphNode(remaining.head.asInstanceOf[MULTIPLICATIVE].value, multiplicativeExprNode)
          remaining = remaining.tail //remove operator token

          val factor_ptr = factor(multiplicativeExprNode)


          //set  SYNTHESIZED attribute
          multiplicativeExpr2_st =
            multiplicativeExprASTnode("sourceString", multiplicativeOP, multiplicativeExpr1_st, factor_ptr)

          //set  SYNTHESIZED attribute  and recurse
          multiplicativeExpr1_ptr = multiplicativeExpr(multiplicativeExprNode, multiplicativeExpr2_st)

        }
        case _ => {
          // throw exception
          throw new ParseException("<multiplicativeExpr> at TOKEN: " + remaining.head.toString()
            + "\nremaining tokens: " + remaining.toString())
        }

      } //  end case match

      return multiplicativeExpr1_ptr //SYNTHESIZED ATTRIIBUTE
    }

    /*
     // attributed  <factor> production rule
      <factor> ::= ident
        Δ <factor>.ptr = leaf(ident.val)
      <factor> ::= num
        Δ <factor>.ptr = leaf(num.val)
      <factor> ::= boollit
        Δ <factor>.ptr = leaf(boollit.val)
      <factor> ::= LP <expression> RP
        Δ <factor>.ptr = <expression>.ptr               
     */
    def factor(pNode: String): ASTnode = {
      // returns all synthesized values
      // TODO: currently returning a Unit. Needs to change to return an ASTnode.
      //    def factor(pNode : String) : Unit = {
      val factorNode = addGraphNode("<factor>", pNode)
      var factorPtr: ASTnode = null

      remaining.headOption match {
        case Some(Ident(_)) => {
          factorPtr = identASTnode(remaining.head.asInstanceOf[Ident].value, remaining.head.asInstanceOf[Ident].value) //AST node creation
          addGraphNode("ident: " + remaining.head.asInstanceOf[Ident].value, factorNode)
          remaining = remaining.tail
        }
        case Some(Num(_)) => {
          factorPtr = numASTnode("source line", remaining.head.asInstanceOf[Num].value.toString()) //AST node
          addGraphNode("num: " + remaining.head.asInstanceOf[Num].value.toString(), factorNode)
          remaining = remaining.tail
        }
        case Some(Boollit(_)) => {
          factorPtr = boollitASTnode("source line", remaining.head.asInstanceOf[Boollit].value) //AST node
          addGraphNode(remaining.head.asInstanceOf[Boollit].value, factorNode)
          remaining = remaining.tail
        }
        case Some(LP) => {
          remaining = remaining.tail
          // TODO: change expression
          //factorPtr = expression(factorNode)
          expression(factorNode)

          if (remaining.head != RP)
            throw new ParseException("<factor> Expected RP, not: " + remaining.head.toString()
              + "\nremaining tokens: " + remaining.toString())
          remaining = remaining.tail
        }
        case _ => throw new ParseException("<factor> at TOKEN: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
      }
      return factorPtr
    }

    //END PRODUCTION DEFINITIONS
    var generatedAST: ASTnode = null

    try {
      generatedAST = program()
      if (!remaining.isEmpty) //make sure the token list is empty
        throw new ParseException("TOKEN STREAM IS NOT EMPTY  starting at: " + remaining.head.toString()
          + "\nremaining tokens: " + remaining.toString())
    }
    finally {
      writer.flush()
      writer.close()
    } // end try
    return generatedAST

  } // end parser


  def main(argv: Array[String]) {

    // INPUT FILES
    //    val fileName = "tl-progs/euclid.tl"
    //    val fileName = "tl-progs/type-error1.tl"
    val fileName = "tl-progs/IF.tl"
    //    val fileName = "tl-progs/simple1.tl"
    //    val fileName = "tl-progs/simple2.tl"
    //    val fileName = "tl-progs/factorize.tl"
    //    val fileName = "tl-progs/fibonacci.tl
    //    val fileName = "tl-progs/sqrt.tl"
    //    val fileName = "tl-progs/simple1.tl"
    //    val fileName = "tl-progs/testcase1.tl"
    //    val fileName = "tl-progs/Assign"

    // scanner
    try {
      //test file
      val source = Source.fromFile(fileName)

      //lexical analysis
      val listOfTokens = scannerTL.tokenizer(source).asInstanceOf[List[ParserTL.Token]]
      println("Successful lexical - Token list \"" + fileName + "\" has been generated")

      //write parse tree to graphic representation file
      val ptDotFile = fileName + "PARSE-ONLY-TEST.dot"

      // parse the tokens that came from scanner into a concrete syntax tree
      val AST_TREE = parser(listOfTokens, ptDotFile)
      println("Successful parse - Parse Tree for \"" + fileName + "\" has been generated")
      println("AST Tree: " + AST_TREE);

    } catch {
      case ParseException(msg) => {
        println("PARSER ERROR in production: " + msg)
      }
      case ScannerException(msg) => {
        println("SCANNER ERROR " + msg)
      }
      case e: Exception => {
        println("Error: " + e.getMessage)
        println("Error: " + e)
      }
    }
  } // end main
}