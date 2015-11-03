/*
 * typeCheckerTL.scala
 * CS5363-E
 * Spring 2015
 * Amulya Battu tester
 * Gabe Fernandez design, developer
 * Shravya Gaddam tester
 * David Holland design, developer
 */
package parser

import java.io._

import parser.ParserTL._

import scala.collection.mutable.{ArrayBuffer, ListBuffer, Map, Seq}

// Labels for SubGraphs
class Label(val labelValue: String)

object ilocCodeGeneratorTL {

  class TypeInfo(var typeOK: Boolean, var identifier_type: String)

  case class codeGenException(message: String) extends Exception(message)

  class ILOC(var ilocValue: String)

  //class ILOC(val ilocValue: String, var DOT : String)

  //THE GRAPH IS A GLOBAL SHARED OBJECT ???
  //LABELS ARE GUARANTEED TO BE DISJOINT, SO THERE IS NO REASON TO HAVE MULLTIPLE SUBGRAPHS
  //AT EACH LEVEL IN THE RECURSION, THE ENVIRONMENT IS IN A SINGLE AND PARTICULAR BLOCK
  //THE GLOBAL currentBlock var IS RESET EACH TIME A NEW BLOCK IS CREATED
  //var currentBlockLabel = new Label("N/A")


  abstract class Code()


  case class StmtSubGraph(val entry: Label, val exit: Label, val blocks: Map[String, Seq[ILOC]]) extends Code

  case class StmtListEmpty() extends Code

  case class Empty() extends Code

  case class ExprSeq(val ilocSeq: Seq[ILOC], register: String) extends Code

  case class IdentCode(val register: String) extends Code

  case class NumCode(val iloc: ILOC, val register: String) extends Code

  case class BoolCode(val iloc: ILOC, val register: String) extends Code

  case class EmptySubGraph() extends Code

  case class EndOfBlock() extends Code

  case class SingleDeclCode(val iloc: ILOC) extends Code

  case class DeclListCode(val ilocSeq: Seq[ILOC]) extends Code

  case class Program(val codeMap: scala.collection.mutable.Map[String, Seq[ILOC]]) extends Code


  case class Expr()

  // Output Files
  var writerAST: PrintWriter = null
  var writerILOC: PrintWriter = null

  // DOT Statments
  var DOTstatements = ArrayBuffer[String]()

  // Registers and Labels
  var registerNum: Int = 0
  var blockNumber: Int = -1
  var nodeNumber: Int = 0
  var DOT_marker: Int = 0

  //create GLOBAL execution graph implemented as a MAP whose keys are block labels and 
  //whose values each contains that block's sequence of  ILOC instructions 
  var graph: scala.collection.mutable.Map[Label, ArrayBuffer[ILOC]] = Map()

  // Register Map
  var registerMap: Map[String, String] = Map()

  // OpCodeMap
  var opCodeMap: Map[String, String] = buildOpCodeMap()

  def initializeAST() {
    registerNum = 0
    blockNumber = 0
    nodeNumber = 0
  }

  def setFileName(fileName: String) {
    // Open file for writing - .A3.cfg.dot
    writerAST = new PrintWriter(new File(fileName))

    // Open ILOC file for writing - .ILOC
    val ILOCFileName = fileName.replace(".A3.cfg.dot", ".ILOC")
    writerILOC = new PrintWriter(new File(ILOCFileName))
  }

  // get unique DOT marker
  def getDOTmarker(): String = {

    return "marker" + (DOT_marker += 1).toString()
  }

  // get fresh register
  def getFreshRegister(): String = {
    // get new register
    val tempReg = registerNum

    // increment register number
    registerNum += 1

    // return fresh register
    return "r" + tempReg

  }

  // get fresh node number
  def getFreshNodeNumber(): String = {
    // get new label
    val tempNodeLabel = nodeNumber

    // increment label number
    nodeNumber += 1

    // return fresh label
    return "n" + nodeNumber
  }

  // get fresh block label
  def getFreshBlockLabel(): Label = {

    // increment block number  
    blockNumber += 1
    var blockLabel = new Label("B" + blockNumber.toString())

    // return fresh label
    return blockLabel

  }

  def getCurrentNodeNumber(): Label = {

    return new Label("n" + nodeNumber)
  }

  def getCurrentBlockNumber(): Label = {

    return new Label("B" + blockNumber)
  }

  def getPreviousBlockNumber(): Label = {
    return new Label("B" + (blockNumber - 1))
  }

  def getNextBlockNumber(): Label = {
    return new Label("B" + (blockNumber + 1))
  }

  def printClosingBlockDOTStatements(): String = {
    return "</table>>,fillcolor=\"/x11/white\",shape=box]\n"
  }

  def printOpeningBlockDOTStatements(blockLabel: String): String = {
    return blockLabel + " [label=<<table border=\"0\"><tr><td border=\"1\" colspan=\"3\">" + blockLabel + "</td></tr>"
  }

  def generateDotStatements(blockList: List[(String, Seq[ILOC])]): ArrayBuffer[String] = {

    // initialize DOT String
    val DOT = ArrayBuffer[String]()
    var lastBlock: String = null
    var newBlockFlag = true

    // DIGRAPH DOT STATEMENTS PREAMBLE
    DOT += "digraph graphviz {" + "\n"
    DOT += "node [shape = none];" + "\n"
    DOT += "edge [tailport = s];" + "\n"
    DOT += "entry" + "\n"
    DOT += "subgraph cluster {" + "\n"
    DOT += "color=\"/x11/white\"" + "\n"

    // initialize lastBlock
    lastBlock = "B1"

    for ((blockLabel, ilocSequence) <- blockList) {

      // determine if starting a new block
      if (newBlockFlag) {
        DOT += printOpeningBlockDOTStatements(blockLabel)
        lastBlock = blockLabel
        newBlockFlag = false
      }

      for (iloc <- ilocSequence) {

        val cleanIloc = iloc.ilocValue.replace(",", "")
        val iC = cleanIloc.split("\\s+")

        // TODO: Ensure all cases are covered for all possible ILOC code instructions (e.g. cmp_GE is missing right now...)
        iC(0) match {

          case "loadI" | "load" | "i2i" | "i2c" | "c2c" | "c2i" => {
            DOT += "<tr><td align=\"left\">" + iC(0) + "</td><td align=\"left\">" + iC(1) + "</td><td align=\"left\">=&gt; " + iC(3) + "</td></tr>"
          }
          case "add" | "sub" | "mult" | "div" | "mod" | "cmp_LE" | "cmp_LT" | "cmp_GT" | "cmp_EQ" | "cmp_GE" | "cmp_NE" => {
            DOT += "<tr><td align=\"left\">" + iC(0) + "</td><td align=\"left\">" + iC(1) + ", " + iC(2) + "</td><td align=\"left\">=&gt; " + iC(4) + "</td></tr>"
          }
          case "readInt" => {
            DOT += "<tr><td align=\"left\">" + iC(0) + "</td><td align=\"left\"></td><td align=\"left\">=&gt; " + iC(2) + "</td></tr>"
          }
          case "writeInt" => {
            DOT += "<tr><td align=\"left\">" + iC(0) + "</td><td align=\"left\">" + iC(1) + "</td><td align=\"left\"></td></tr>"
          }
          case "cbr" => {
            DOT += "<tr><td align=\"left\">" + iC(0) + "</td><td align=\"left\">" + iC(1) + "</td><td align=\"left\">-&gt; " + iC(3) + ", " + iC(4) + "</td></tr></table>>,fillcolor=\"/x11/white\",shape=box]\n"
            DOT += lastBlock + " -> " + iC(3) + "\n"
            DOT += lastBlock + " -> " + iC(4) + "\n"
            newBlockFlag = true
          }
          case "jumpI" | "jump" => {
            DOT += "<tr><td align=\"left\">" + iC(0) + "</td><td align=\"left\"></td><td align=\"left\">-&gt; " + iC(2) + "</td></tr></table>>,fillcolor=\"/x11/white\",shape=box]\n"
            DOT += lastBlock + " -> " + iC(2) + "\n"
            newBlockFlag = true
          }
          case "exit" => {
            DOT += "<tr><td align=\"left\">exit</td><td align=\"left\"></td><td align=\"left\"></td></tr></table>>,fillcolor=\"/x11/white\",shape=box]\n}\n"
            DOT += "entry -> B1\n"
            DOT += lastBlock + " -> exit\n}"
          }
          case _ => {
            println("ERROR -> unable to complete DOT statement generation successfully")
          }
        }
      }
    }

    /* TESTING OUTPUT
    for (line <- DOT) {
      println(line)
    }
    */

    return DOT
  }

  /*
  def mergeILOCInBlock(blockMap1: Map[String, Seq[ILOC]], blockMap2: Map[String, Seq[ILOC]]): Map[String, Seq[ILOC]] = {

    var ilocSeq: Seq[ILOC] = Seq()

    blockMap1.foreach((e: (String, Seq[ILOC])) => {
      //get arraybuffer based on key, if it exists
      if (blockMap2.get(e._1) != None) {
        ilocSeq = blockMap2(e._1)

        // add it to arrayBuffer in this block
        ilocSeq = e._2 ++ ilocSeq

        // replace array buffer with new merged array buffer
        blockMap1(e._1) = ilocSeq
      }
    })

    // copy over additional kvs into BlockMap1 that only exist in BlockMap2
    blockMap2.foreach((e: (String, Seq[ILOC])) => {
      //check if key is in 2 that is not in 1
      if (blockMap1.get(e._1) == None) {
        blockMap1(e._1) = blockMap2(e._1)
      }
    })

    return blockMap1
  }
  * 
  */

  //function that recursively walks the AST tree Depth-First, PostOrder generating blocks of ILOC sequences
  //and a control flow graph, which depicts blocks as nodes, and edges as control flows between blocks 
  def genCode(node: ASTnode): Code = {

    node match {

      //program -> declsList stmtList
      case programASTnode(_, declsList, stmtList) => {

        //initialize globals
        DOTstatements = ArrayBuffer[String]()

        var entry = getFreshBlockLabel()

        //Generate decl list
        val declSeq = genCode(declsList)

        // Generate stmt list, which returns programMap
        var subgraphStmtSeq = genCode(stmtList)
        val stmtListEntry = subgraphStmtSeq.asInstanceOf[StmtSubGraph].entry
        val stmtListExit = subgraphStmtSeq.asInstanceOf[StmtSubGraph].exit
        val programMap = subgraphStmtSeq.asInstanceOf[StmtSubGraph].blocks

        //prepend new 1st block into programMap, with jump to stmtList entry block
        programMap += (entry.labelValue -> (declSeq.asInstanceOf[DeclListCode].ilocSeq :+ new ILOC("jumpI -> " + stmtListEntry.labelValue)))

        //append "exit" onto end of stmtListExit block
        var lastBlock = programMap(stmtListExit.labelValue) :+ new ILOC("exit")
        programMap += (stmtListExit.labelValue -> lastBlock)

        var sortedBlock = programMap.toList.sortWith { (x, y) =>
          x._1.replace("B", "").toInt < y._1.replace("B", "").toInt
        }


        // THIS WORKS NOW :)
        var sortedBlockBuffer = sortedBlock.to[ListBuffer]

        //post process map
        var previous = sortedBlockBuffer.last
        for (i <- (0 to (sortedBlock.length - 2)).reverse) {
          //  must count backwards, because list size is shrinking

          var currentBlockTuple = sortedBlockBuffer.apply(i) // tuple:   (label : String,  Seq[ILOC])

          //if( currentBlockTuple._2.last.ilocValue == ("jumpI -> " + previous._1) && previous._2.head.ilocValue.startsWith("jumpI") ) {
          if (currentBlockTuple._2.last.ilocValue == ("jumpI -> " + previous._1) && countJumps(previous._1, sortedBlockBuffer)) {

            // delete last instruction of current block and append all instructions of previous block (if any),
            // then remove current block from list
            val mergedILOC = currentBlockTuple._2.dropRight(1) ++ previous._2
            val tuple = (currentBlockTuple._1, mergedILOC)
            sortedBlockBuffer.remove(i) //remove old version of current block
            sortedBlockBuffer.insert(i, tuple)
            sortedBlockBuffer.remove(i + 1)
          }

          previous = sortedBlockBuffer.apply(i)
        }

        //cast BufferList back to Sequence List
        sortedBlock = sortedBlockBuffer.to[List]

        //used to determine if a label is referenced by more than one ILOC instruction
        def countJumps(label: String, list: ListBuffer[(String, Seq[ILOC])]): Boolean = {

          var counter = 0

          for (tuple <- list) {

            for (iloc <- tuple._2) {
              //if (iloc.ilocValue.contains(label)) {
              if (iloc.ilocValue.endsWith(label)) {
                counter = counter + 1
              }

            }

          }

          return (counter == 1)
        } // end countJumps

        for ((key, sequence) <- sortedBlock) {
          // Print out/write out label
          println(key + ":")
          writerILOC.write(key + ":\n")

          // Print out/write out ILOC sequence
          sequence.map { x => println("  " + x.ilocValue) }
          sequence.map { x => writerILOC.write("  " + x.ilocValue + "\n") }
          writerILOC.write("\n")
        }

        //        println("*************************** END OF MAP DUMP  ")
        //        println("  ")

        // generate DOT Statements
        val newDots = generateDotStatements(sortedBlock)

        //write ArrayBuffer out to DOT file
        for (statement <- newDots) {
          writerAST.write(statement)
        }

        // Close output files
        writerAST.flush()
        writerAST.close()
        writerILOC.flush()
        writerILOC.close()

        println("  ")
        println("*************************** MIPS CODE   ")
        println("  ")
        // Generate MIPS Code using BlockMap of full ILOC Code
        mipsGeneratorTL.genMIPS(sortedBlock)

        return Program(programMap)

      } // end case programASTnode

      //declsList -> decl declsList | ε
      case declarationsListASTnode(_, declaration, declarationList) => {

        var ilocSeq = Seq[ILOC]()

        declarationList match {
          case AST_epsilon() => {
            //end of declarations list, do nothing
            ilocSeq = Seq[ILOC]() //create empty Seq to be passed back up recursive call stack
          }
          case declarationsListASTnode(_, _, _) => {
            val declListCode = genCode(declarationList)
            declListCode match {
              case DeclListCode(ilocSeq_) => {
                ilocSeq ++= ilocSeq_ //append previous list
              }
              case _ => {
                throw new codeGenException("declListCode error, " + declarationList.toString())
              }
            } //end match declListCode
          }
          case _ => {
            throw new codeGenException("declarationList error, " + declarationList.toString())
          }
        } //end match


        // get single ILOC from SingleDeclCode
        val singleDecl = genCode(declaration)
        singleDecl match {
          case SingleDeclCode(iloc) => {
            //2 +: seq   to prepend '2' to sequence
            ilocSeq = iloc +: ilocSeq
          }
          case _ => {
            throw new codeGenException("declaration error, " + declaration.toString())
          }
        } //end match

        //return DeclList sequence of ILOC declarations
        return DeclListCode(ilocSeq) //add last declaration to list

      } //end case delcarationsListASTnode

      //decl -> ident type
      case declartionASTnode(label, ident, type_) => {

        /*
              * get a fresh register
              * load the register with ident
              * put the register in registerTable
              */

        //var register = "r_" + ident.asInstanceOf[identASTnode].value
        val register = getFreshRegister()

        registerMap += (ident.asInstanceOf[identASTnode].value -> register)

        var iloc: ILOC = null

        type_ match {

          case numASTnode(_, value) => {
            // assign 0
            iloc = new ILOC("loadI 0 => " + register)
          }

          case boollitASTnode(_, value) => {
            // assign false
            iloc = new ILOC("loadI false => " + register)
          }

          case _ => {
            //error
            throw new codeGenException("Declaration Error, unexpected type. Expected INT or BOOL, received: " + type_.toString())
          }
        }

        // return iloc as DeclSubGraph
        return SingleDeclCode(iloc)
      }

      //stmtList -> stmt stmtList | ε
      case statementListASTnode(_, statement, statementList) => {


        var mergedBlocks: Map[String, Seq[ILOC]] = Map()
        var ilocSeq: Seq[ILOC] = Seq()

        var stmtSubGraphBlocks: Map[String, Seq[ILOC]] = null
        var stmtSubGraphEntry: Label = null
        var stmtSubGraphExit: Label = null
        var restSubGraphBlocks: Map[String, Seq[ILOC]] = null
        var restSubGraphEntry: Label = null
        var restSubGraphExit: Label = null

        //generate ILOC code for the single statement
        val stmtSubGraph = genCode(statement)

        stmtSubGraph match {
          case StmtSubGraph(entry, exit, blocks) => {

            stmtSubGraphEntry = entry
            stmtSubGraphExit = exit
            stmtSubGraphBlocks = blocks

          }
          case _ => {
            throw new codeGenException("StmtList error, " + statement.toString())
          }
        }


        if (statementList.isInstanceOf[AST_epsilon]) {

          genCode(statementList) //eat AST node, recursion tail

          //in epsilon case just return the simple statement
          return StmtSubGraph(stmtSubGraphEntry, stmtSubGraphExit, stmtSubGraphBlocks)

          /*
          restSubGraphEntry = getFreshBlockLabel()
          restSubGraphExit = restSubGraphEntry
          restSubGraphBlocks  = Map()
          val seq : Seq[ILOC] = Seq()
          restSubGraphBlocks += (restSubGraphEntry.labelValue -> seq)
          *
          */


        }
        else if (statementList.isInstanceOf[statementListASTnode]) {

          val restStatementList = genCode(statementList)

          restSubGraphEntry = restStatementList.asInstanceOf[StmtSubGraph].entry
          restSubGraphExit = restStatementList.asInstanceOf[StmtSubGraph].exit
          restSubGraphBlocks = restStatementList.asInstanceOf[StmtSubGraph].blocks
        }
        else
          throw new codeGenException("StmtList error, " + statementList.toString())


        val newBlock = stmtSubGraphBlocks(stmtSubGraphExit.labelValue) ++ restSubGraphBlocks(restSubGraphEntry.labelValue)

        mergedBlocks = (stmtSubGraphBlocks - stmtSubGraphExit.labelValue) ++ (restSubGraphBlocks - restSubGraphEntry.labelValue)
        mergedBlocks += (stmtSubGraphExit.labelValue -> newBlock)

        //output merged subgraphs as new super-graph
        return StmtSubGraph(stmtSubGraphEntry, restSubGraphExit, mergedBlocks)
      }

      //if : stmt -> expr thenStmts elseClause
      case IfStatementASTnode(_, expression, thenStmtList, elseStmtList) => {

        /*
          Outline:
        
          1. generate ILOC sequence for "condition" expression, call this condInsts and note the resultRegister
          
          2. entry = fresh label
          
          3. generate SubGraph for "then" statements, call this thenPart
          
          4. generate SubGraph for "else" statements, call this elsePart
          
          5. after = fresh label
          
          6. condBlock = condInsts + cbr(condInsts, thenPart.entry, elsePart.enty)
          
          7. thenComplete = thenPart.blocks(thenPart.exit) + jumpI(after)
          
          8. elseComplete = elsePart.blocks(elsePart.exit) + jumpI(after)
          
            create new SubGraph(
              entry,
              after,
              (thenPart.blocks - thenPart.exit)
                ++ (elsePart.blocks - elsePart.exit)
                ++ { thenPart.exit => thenComplete
                      elsePart.exit => elseComplete
                      entry => condBlock
                      after => Seq()
                   }
              )
          * 
          */

        val newEntry = getFreshBlockLabel()
        var superGraph: StmtSubGraph = null

        val exprSeq = genCode(expression) //get expression

        val condInsts = exprSeq.asInstanceOf[ExprSeq].ilocSeq
        val resultRegister = exprSeq.asInstanceOf[ExprSeq].register


        val thenPart = genCode(thenStmtList) //get then statements
        val entryThenPart = thenPart.asInstanceOf[StmtSubGraph].entry.labelValue
        val exitThenPart = thenPart.asInstanceOf[StmtSubGraph].exit.labelValue
        val thenPartBlocks: Map[String, Seq[ILOC]] = thenPart.asInstanceOf[StmtSubGraph].blocks


        if (!elseStmtList.isInstanceOf[AST_epsilon]) {
          //THERE IS AN ELSE PART

          val elsePart = genCode(elseStmtList) //get elseClause statements
          if (!elsePart.isInstanceOf[StmtSubGraph]) {
            throw new codeGenException("ELSE CLAUSE error: " + elseStmtList.toString())
          }

          val after = getFreshBlockLabel() //get 'after' after call to generate elseStmtList

          val entryElsePart = elsePart.asInstanceOf[StmtSubGraph].entry.labelValue
          val exitElsePart = elsePart.asInstanceOf[StmtSubGraph].exit.labelValue
          val elsePartBlocks = elsePart.asInstanceOf[StmtSubGraph].blocks


          val condBlock = condInsts :+ new ILOC("cbr " + resultRegister + " -> " + entryThenPart + ", " + entryElsePart)
          val regFieldsAndLabels = resultRegister + ", " + entryThenPart + ", " + entryElsePart

          //OR pair a DOT statement in ILOC with each machine instruction
          //class ILOC(val ilocValue: String, val DOT : String)

          val thenComplete = thenPartBlocks(exitThenPart) :+ new ILOC("jumpI -> " + after.labelValue)
          val elseComplete = elsePartBlocks(exitElsePart) :+ new ILOC("jumpI -> " + after.labelValue)

          var mergedMap = (thenPartBlocks - exitThenPart) ++ (elsePartBlocks - exitElsePart)
          mergedMap += (exitThenPart -> thenComplete)
          mergedMap += (exitElsePart -> elseComplete)
          mergedMap += (newEntry.labelValue -> condBlock)
          mergedMap += (after.labelValue -> Seq())

          /*
          val mergedMap : Map[String, Seq[ILOC]]
           = (thenPartBlocks - exitThenPart)  ++
             (elsePartBlocks - exitElsePart)  +
             { (exitThenPart -> thenComplete)
               (exitElsePart -> elseComplete)
               (newEntry.labelValue -> condBlock)
               (after.labelValue -> Seq[ILOC]())
             }
             *
             */

          //return the  constructed IfStmtSubGraph that had both an IF and Else part
          superGraph = StmtSubGraph(newEntry, after, mergedMap)

        } else {
          //EMPTY ELSE,  MUST jumpI TO 'AFTER' WHEN CONDITION FAILS

          val after = getFreshBlockLabel()

          //build condition block
          val condBlock = condInsts :+ new ILOC("cbr " + resultRegister + " -> " + entryThenPart + ", " + after.labelValue)

          //append sequence with key 'exitThenPart' with 'jumpI after'
          val thenComplete = thenPartBlocks(exitThenPart) :+ new ILOC("jumpI -> " + after.labelValue)

          var mergedMap = thenPartBlocks - exitThenPart
          mergedMap += (exitThenPart -> thenComplete)
          mergedMap += (newEntry.labelValue -> condBlock)
          mergedMap += (after.labelValue -> Seq())

          //return the  constructed IfStmtSubGraph that only had an IF part
          superGraph = StmtSubGraph(newEntry, after, mergedMap)
        }

        return superGraph

      } // end case IfStatementASTnode

      //else: stmt -> stmtList | ε
      case ElseClauseStatementASTnode(_, statementListElse) => {

        val subgraphStmtList = genCode(statementListElse)

        subgraphStmtList match {
          case StmtSubGraph(entryElse, exitElse, blocksElse) => {

            return StmtSubGraph(entryElse, exitElse, blocksElse)
          }

          case _ => {
            throw new codeGenException("ELSE CLAUSE error: " + statementListElse.toString())
          }
        }

      } //end case ELSE

      //while : stmt -> expr stmtList
      case WhileStatementASTnode(_, expression, statementList) => {

        /*

        Outline:
          1. generate ILOC sequence for "condition" expression, call this condInsts and note the resultRegister
          2. entry = fresh label
          3. after = fresh label
          4. generate SubGraph for "do" statements, call this doPart
          5. condBlock = condInsts + cbr(condInsts, doPart.entry)
          6. doComplete = doPart.blocks(doPart.exit) + jumpI(after)

          7.
          create new SubGraph(
            entry,
            after,
            (doPart.blocks - doPart.exit)
            ++ { doPart.exit => doComplete
                  entry => condBlock
                  after => Seq()
               }
           )

         */

        // Generate new block now
        var mergedMap: Map[String, Seq[ILOC]] = Map()
        var ilocSeq: Seq[ILOC] = Seq()

        // 1. generate ILOC sequence for "condition" expression, call this condInsts and note the resultRegister
        val condition = genCode(expression)
        val resultRegister = condition.asInstanceOf[ExprSeq].register
        val condInst = condition.asInstanceOf[ExprSeq].ilocSeq

        // 2. entry = fresh label
        val entry = getFreshBlockLabel()
        val conditional = getFreshBlockLabel() //conditional gets its own separate block, which empty entry block jumps to
        val jumpI_toConditional = new ILOC("jumpI -> " + conditional.labelValue)

        // 4. generate SubGraph for "do" statements, call this doPart
        val doPart = genCode(statementList)
        val doEntry = doPart.asInstanceOf[StmtSubGraph].entry
        val doExit = doPart.asInstanceOf[StmtSubGraph].exit
        val doBlocks = doPart.asInstanceOf[StmtSubGraph].blocks

        // 3. after = fresh label
        val after = getFreshBlockLabel()

        // 5. condBlock = condInsts + cbr(condInsts, doPart.entry, after)
        val cbr = new ILOC("cbr " + resultRegister + " -> " + doEntry.labelValue + ", " + after.labelValue)
        val condBlock = condInst :+ cbr

        // 6. doComplete = doPart.blocks(doPart.exit) + jumpI(condBlock)
        val doComplete = doBlocks(doExit.labelValue) :+ jumpI_toConditional

        //*7.
        mergedMap = (doBlocks - doExit.labelValue)
        mergedMap += (entry.labelValue -> (Seq() :+ jumpI_toConditional)) //load entry block with jump to conditional block
        mergedMap += (doExit.labelValue -> doComplete)
        mergedMap += (conditional.labelValue -> condBlock) //load conditional block into map
        mergedMap += (after.labelValue -> Seq()) //load empty exit block into map


        //return the  constructed IfStmtSubGraph that only had an IF part
        return StmtSubGraph(entry, after, mergedMap)

      } // end WhileStatementASTnode

      //'WRITEINT' : stmt -> WRITEINT expr
      case WRITEINT_ASTnode(_, expression) => {

        var blocks: Map[String, Seq[ILOC]] = Map()
        var ilocSeq: Seq[ILOC] = Seq()

        //Same entry and exit block.
        //This is not an if, or while, but is a statement that must return entry/exit.
        val Entry = getFreshBlockLabel()
        val Exit = getFreshBlockLabel()

        val subgraphExpr = genCode(expression)

        subgraphExpr match {
          case ExprSeq(ilocs, register) => {

            // Add instructions from expression to Seq[ILOC]
            ilocSeq = ilocSeq ++ ilocs

            // Add writeint  to ilocSeq with resultant register
            ilocSeq = ilocSeq :+ new ILOC("writeInt " + register)

          }
          case NumCode(ilocNum, registerNum) => {
              // add iloc to sequence example:   writeInt 3
              ilocSeq = ilocSeq :+ ilocNum
              ilocSeq = ilocSeq :+ new ILOC("writeInt " + registerNum)
            }
          case IdentCode(register) => {

            // Add writeint  to ilocSeq with resultant register
            ilocSeq = ilocSeq :+ new ILOC("writeInt " + register)

          }
          case _ => {
            throw new codeGenException("WRITEINT expression error: " + expression.toString())
          }
        }


        //Entry block jumps to Exit block
        ilocSeq = ilocSeq :+ new ILOC("jumpI -> " + Exit.labelValue)

        //load entry block into map
        blocks += (Entry.labelValue -> ilocSeq)

        //load an empty block into the map using Exit key
        blocks += (Exit.labelValue -> Seq())

        return StmtSubGraph(Entry, Exit, blocks)

      }

      //':=' : stmt -> ident expr
      case assignmentASTnode(label, identASGN, expr) => {

        var blocksASGN: Map[String, Seq[ILOC]] = Map()
        var ilocSeqASGN: Seq[ILOC] = Seq()
        var iloc: ILOC = null
        var resultRegisterASGN: String = null
        var subgraphASGN: StmtSubGraph = null

        //Same entry and exit block. This is not an if, or while, but is a statement that must return entry/exit.
        val entryASGN = getFreshBlockLabel()
        val exitASGN = getFreshBlockLabel()

        // handle the READINT case
        if (label.contains("READINT")) {
          //case READINT X

          // get register for ident
          val code = genCode(identASGN)
          code match {
            case IdentCode(register) => {
              resultRegisterASGN = register
            }
            case _ => {
              throw new codeGenException("READINT assignment ident, type error: " + identASGN.toString())
            }
          }

          // add instruction to ILOC array
          iloc = new ILOC("readInt => " + resultRegisterASGN)

          // add 'readInt' and 'jumpI' instructions to to sequence
          ilocSeqASGN = ilocSeqASGN :+ iloc
          ilocSeqASGN = ilocSeqASGN :+ new ILOC("jumpI -> " + exitASGN.labelValue)

          // add ilocSeq to block map
          blocksASGN += (entryASGN.labelValue -> ilocSeqASGN)
          //load an empty block into the map using Exit key
          blocksASGN += (exitASGN.labelValue -> Seq())

          //construct subgraph
          subgraphASGN = StmtSubGraph(entryASGN, exitASGN, blocksASGN)

        } else {
          //must be a real assignment like   X := 5

          val subgraphExprASGN = genCode(expr)

          // Otherwise, handle assignment to ident
          subgraphExprASGN match {
            // assigning num to ident
            case NumCode(ilocNum, registerNum) => {
              // add iloc to sequence   val b = a :+ 2
              ilocSeqASGN = ilocSeqASGN :+ ilocNum
              resultRegisterASGN = registerNum
            }
            case IdentCode(registerIdent) => {
              resultRegisterASGN = registerIdent
            }
            //assigning bool to ident
            case BoolCode(ilocBool, registerBool) => {
              ilocSeqASGN = ilocSeqASGN :+ ilocBool
              resultRegisterASGN = registerBool
            }
            // assigning expr to ident
            case ExprSeq(iloc_seq, register) => {
              // add iloc to sequence
              ilocSeqASGN = ilocSeqASGN ++ iloc_seq
              resultRegisterASGN = register
            }
            case _ => {
              throw new codeGenException("assignment expr error: " + expr.toString())
            }
          } // end match subgrahExpr

          val code = genCode(identASGN)
          code match {
            case IdentCode(register) => {
              // create new iloc instruction to assign right-handside to Ident; grabbing register value for Ident
              ilocSeqASGN = ilocSeqASGN :+ new ILOC("i2i " + resultRegisterASGN + " => " + register)
            }
            case _ => {
              throw new codeGenException("assignment ident, type error: " + identASGN.toString())
            }
          }

          //append jumpI
          ilocSeqASGN = ilocSeqASGN :+ new ILOC("jumpI -> " + exitASGN.labelValue)

          blocksASGN += (entryASGN.labelValue -> ilocSeqASGN)
          //load an empty block into the map using Exit key
          blocksASGN += (exitASGN.labelValue -> Seq())

          //construct subgraph
          subgraphASGN = StmtSubGraph(entryASGN, exitASGN, blocksASGN)

        } //end if-then-else

        return subgraphASGN

      } //end case AssignmentASTnode

      //'*'  :  expr -> leftExpr rightExpr
      //'div':  expr -> leftExpr rightExpr
      //'mod':  expr -> leftExpr rightExpr
      case multiplicativeExprASTnode(_, operator, leftExpr, rightExpr) => {

        /*
           * For a binary multiplicative operation
                recursively, generate the code for the left child, note the result register
                recursively, generate the code for the right child, note the result register
                get a fresh register for the result
                generate code that takes the inputs from the registers noted in 1 and 2, performs the operation, and puts the result in the register obtained in 3
                append together the code from 1, 2, and 4.
                return the code from 5 together with the register from 3.
           */

        val Left = genCode(leftExpr)
        val Right = genCode(rightExpr)

        //NO NEW BLOCK FOR EXPRESSIONS 
        //DOTstatements += "blockEntry [label=<<table border=\"0\"><tr><td border=\"1\" colspan=\"3\">" + blockEntry + "</td></tr><tr>"

        var ilocSeqMULT: Seq[ILOC] = Seq()
        var returnRegister = ""
        var leftRegister = ""
        var rightRegister = ""

        // check operator,    No BOOL case here with '*' or 'div'
        if (operator == "*" || operator == "div") {

          //processExpr(subgraphLeft)
          Left match {
            case IdentCode(identRegister) => {
              leftRegister = identRegister
            }
            case NumCode(ilocMULT, register) => {
              ilocSeqMULT = ilocSeqMULT :+ ilocMULT
              leftRegister = register
            }
            case BoolCode(iloc, register) => {
              throw new codeGenException("MULTIPLICATIVE type error, BOOL not allowed for operation: " + leftExpr.toString())
            }
            case ExprSeq(iloc_seq, register) => {
              ilocSeqMULT = iloc_seq
              leftRegister = register
            }
            case _ => {
              throw new codeGenException("MULTIPLICATIVE error: " + leftExpr.toString())
            }
          }

          //processExpr(subgraphRight)
          Right match {
            case IdentCode(identRegister) => {
              returnRegister = getFreshRegister()
              ilocSeqMULT = ilocSeqMULT :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + identRegister + " => " + returnRegister)
            }
            case NumCode(iloc, register) => {
              returnRegister = getFreshRegister()
              ilocSeqMULT = ilocSeqMULT :+ iloc
              ilocSeqMULT = ilocSeqMULT :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + register + " => " + returnRegister)
            }
            case BoolCode(iloc, register) => {
              throw new codeGenException("MULTIPLICATIVE type error, BOOL not allowed for operation: " + rightExpr.toString())
            }
            case ExprSeq(iloc_seq, register) => {
              returnRegister = getFreshRegister()
              ilocSeqMULT = ilocSeqMULT ++ iloc_seq
              ilocSeqMULT = ilocSeqMULT :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + register + " => " + returnRegister)
            }
            case _ => {
              throw new codeGenException("MULIPLICATIVE error: " + rightExpr.toString())
            }
          }

        } else if (operator == "mod") {

          def Mod(leftRegister: String, rightRegister: String): (String, Seq[ILOC]) = {
            // returns a tuple

            val regDiv = getFreshRegister()
            var seq = Seq(new ILOC("div " + leftRegister + " " + rightRegister + " => " + regDiv))
            val regMult = getFreshRegister()
            seq = seq :+ new ILOC("mult " + regDiv + " " + rightRegister + " => " + regMult)
            val regSub = getFreshRegister()
            seq = seq :+ new ILOC("sub " + leftRegister + " " + regMult + " => " + regSub)


            return (regSub, seq)
          }

          //processExpr(subgraphLeft)
          Left match {
            case IdentCode(identRegister) => {
              leftRegister = identRegister
            }
            case NumCode(ilocMULT, register) => {
              ilocSeqMULT = ilocSeqMULT :+ ilocMULT
              leftRegister = register
            }
            case BoolCode(iloc, register) => {
              throw new codeGenException("MULTIPLICATIVE type error, BOOL not allowed for operation: " + leftExpr.toString())
            }
            case ExprSeq(iloc_seq, register) => {
              ilocSeqMULT = iloc_seq
              leftRegister = register
            }
            case _ => {
              throw new codeGenException("MULTIPLICATIVE error: " + leftExpr.toString())
            }
          }

          //processExpr(subgraphRight)
          Right match {
            case IdentCode(identRegister) => {
              val tuple = Mod(leftRegister, identRegister)
              ilocSeqMULT = ilocSeqMULT ++ tuple._2
              returnRegister = tuple._1
            }
            case NumCode(iloc, register) => {
              ilocSeqMULT = ilocSeqMULT :+ iloc
              val tuple = Mod(leftRegister, register)
              ilocSeqMULT = ilocSeqMULT ++ tuple._2
              returnRegister = tuple._1
            }
            case BoolCode(iloc, register) => {
              throw new codeGenException("MULTIPLICATIVE type error, BOOL not allowed for operation: " + rightExpr.toString())
            }
            case ExprSeq(iloc_seq, register) => {
              ilocSeqMULT = ilocSeqMULT ++ iloc_seq
              val tuple = Mod(leftRegister, register)
              ilocSeqMULT = ilocSeqMULT ++ tuple._2
              returnRegister = tuple._1
            }
            case _ => {
              throw new codeGenException("MULIPLICATIVE error: " + rightExpr.toString())
            }
          }

        } else {
          throw new codeGenException("MULTIPLICATIVE EXPRESSION error: " + operator.toString() + ", " + leftExpr.toString() + ", " + rightExpr.toString())
        }

        return ExprSeq(ilocSeqMULT, returnRegister)

      }

      //'='  :  expr -> leftExpr rightExpr             CAN HAVE BOOL OPERANDS
      //'<'  :  expr -> leftExpr rightExpr   NOT BOOL
      //'>'  :  expr -> leftExpr rightExpr   NOT BOOL
      //'!=' :  expr -> leftExpr rightExpr             CAN HAVE BOOL OPERANDS
      //'<=' :  expr -> leftExpr rightExpr   NOT BOOL
      //'>=  :  expr -> leftExpr rightExpr   NOT BOOL
      case compareExprASTnode(_, operator, leftExpr, rightExpr) => {

        val subgraphLeft = genCode(leftExpr)
        val subgraphRight = genCode(rightExpr)

        val opCode = opCodeMap(operator)


        var ilocSeq: Seq[ILOC] = Seq()
        var iloc: ILOC = null
        var returnRegister = ""
        var leftRegister = ""
        var rightRegister = ""

        subgraphLeft match {
          case IdentCode(identRegister) => {
            leftRegister = identRegister
          }
          case NumCode(iloc, register) => {
            ilocSeq = ilocSeq :+ iloc
            leftRegister = register

          }
          case BoolCode(iloc, register) => {
            ilocSeq = ilocSeq :+ iloc
            leftRegister = register
          }
          case ExprSeq(exprIlocSeq, register) => {
            ilocSeq = ilocSeq ++ exprIlocSeq
            leftRegister = register
          }
          case _ => {
            throw new codeGenException("COMPARATIVE error: " + leftExpr.toString())
          }
        }

        subgraphRight match {
          case IdentCode(identRegister) => {
            returnRegister = getFreshRegister()
            ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + identRegister + " => " + returnRegister)

          }
          case NumCode(iloc, register) => {
            ilocSeq = ilocSeq :+ iloc
            returnRegister = getFreshRegister()
            rightRegister = register
            ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + rightRegister + " => " + returnRegister)
          }
          case BoolCode(iloc, register) => {
            // ONLY IF OPERATOR IS '='  or '!=' and both operand types are Bool
            if (operator == "!=" || operator == "=") {
              //type checking should have already caught this
              ilocSeq = ilocSeq :+ iloc
              returnRegister = getFreshRegister()
              rightRegister = register
              ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + rightRegister + " => " + returnRegister)
            }
            else {
              throw new codeGenException("COMPARE EXPRESSION error: " + operator.toString() + ", " + leftExpr.toString() + ", " + rightExpr.toString())
            }
          }
          case ExprSeq(exprIlocSeq, register) => {
            returnRegister = getFreshRegister()
            ilocSeq = ilocSeq ++ exprIlocSeq
            ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + register + " => " + returnRegister)
          }
          case _ => {
            throw new codeGenException("COMPARATIVE error: " + rightExpr.toString())
          }
        }

        return ExprSeq(ilocSeq, returnRegister)

      }

      //'+'  :  expr -> leftExpr rightExpr
      //'-'  :  expr -> leftExpr rightExpr
      case additiveExprASTnode(_, operator, leftExpr, rightExpr) => {

        val subgraphLeft = genCode(leftExpr)
        val subgraphRight = genCode(rightExpr)

        var ilocSeq: Seq[ILOC] = Seq()
        var returnRegister = ""
        var leftRegister = ""
        var rightRegister = ""

        // check operator
        if (operator == "+" || operator == "-") {
          /*
           * add r0 r1 => r2
           * <tr><td align="left">add</td><td align="left">r0, r_X</td><td align="left">=&gt; r1</td></tr>
           */

          //processExpr(subgraphLeft)
          //processExpr(subgraphRight)
          subgraphLeft match {
            case IdentCode(identRegister) => {
              leftRegister = identRegister
            }
            case NumCode(iloc, register) => {
              ilocSeq = ilocSeq :+ subgraphLeft.asInstanceOf[NumCode].iloc
              leftRegister = register

            }
            case BoolCode(iloc, register) => {
              throw new codeGenException("ADDITIVE type error, BOOL not allowed for operation: " + leftExpr.toString())
            }
            case ExprSeq(exprIlocSeq, register) => {
              ilocSeq = exprIlocSeq
              leftRegister = register
            }
            case _ => {
              throw new codeGenException("ADDITIVE error: " + leftExpr.toString())
            }

          }

          subgraphRight match {
            case IdentCode(identRegister) => {
              returnRegister = getFreshRegister()
              ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + identRegister + " => " + returnRegister)

            }
            case NumCode(iloc, register) => {
              returnRegister = getFreshRegister()
              ilocSeq = ilocSeq :+ subgraphRight.asInstanceOf[NumCode].iloc
              ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + register + " => " + returnRegister)
              //TODO: Consider adding the "i2i r4 => r_SQRT" ILOC. Note: Jeff said this was not necessary...?
            }
            case BoolCode(iloc, register) => {
              throw new codeGenException("ADDITIVE type error, BOOL not allowed for operation: " + rightExpr.toString())

            }
            case ExprSeq(exprIlocSeq, register) => {
              returnRegister = getFreshRegister()
              ilocSeq = ilocSeq ++ exprIlocSeq
              ilocSeq = ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + register + " => " + returnRegister)
            }

          }

        } else {
          // mark - throw exception
          // TODO: add exception handler
        }

        return ExprSeq(ilocSeq, returnRegister)

      }

      //ident : expr -> ε
      case identASTnode(_, value) => {

        // get register out of registerTable
        val opRegister = registerMap(value)

        // create subgraph, returning the value as the subgraph
        return new IdentCode(opRegister)

      }

      //num : expr -> ε
      case numASTnode(_, value) => {

        // get fresh register
        val register = getFreshRegister()

        // construct ILOC
        val iloc = new ILOC("loadI " + value + " => " + register)

        // create subgraph, returning the value as the subgraph
        val subGraph = new NumCode(iloc, register)

        return subGraph
      }

      //boollit : expr -> ε
      case boollitASTnode(_, value) => {

        // get fresh register
        val register = getFreshRegister()

        // construct ILOC
        val iloc = new ILOC("loadI " + value + " => " + register)

        // create subgraph, returning the value as the subgraph
        val subGraph = new BoolCode(iloc, register)

        return subGraph

      }

      // ε
      case AST_epsilon() => {
        // epsilon or the null case
        // create subgraph, returning the value as the subgraph
        val empty = new Empty()

        return empty
      }

      case _ => {
        var msg: String = "";
        if (node != null) {
          msg = node.toString()
          throw new codeGenException("UNKNOWN AST NODE TYPE " + "\n" + msg + "\n")
        } else {
          throw new codeGenException("TEST NODE IS NULL " + msg + "\n")
        }
      } // end case _

    } // end BIG OUTER match

    //TODO (REMOVE)
    new EmptySubGraph()

  } // genCode()

  /**
   * *******
   * def processEpxr(subgraphExpr: SubGraph): Array[ILOC] = {
   * val ilocArray = new ArrayBuffer[ILOC]()
   * subgraphExpr match {
   * case IdentCode(identRegister) => {
   *
   * }
   * case NumCode(iloc, register) => {
   * ilocArray += subgraphExpr.asInstanceOf[NumCode].iloc
   * leftRegister = register
   *
   * }
   * case BoolCode(iloc, register) => {
   *
   * }
   * case ExprSeq(ilocArray, register) => {
   *
   * }
   *
   * }
   *
   * return ilocArray
   * }
   */

  def buildOpCodeMap(): Map[String, String] = {

    var opCodeMap: Map[String, String] = Map()
    opCodeMap += ("=" -> "cmp_EQ")
    opCodeMap += ("<" -> "cmp_LT")
    opCodeMap += (">" -> "cmp_GT")
    opCodeMap += ("!=" -> "cmp_NE")
    opCodeMap += ("<=" -> "cmp_LE")
    opCodeMap += (">=" -> "cmp_GE")
    opCodeMap += ("*" -> "mult")
    opCodeMap += ("div" -> "div")
    opCodeMap += ("mod" -> "mod")
    opCodeMap += ("+" -> "add")
    opCodeMap += ("-" -> "sub")

    return opCodeMap
  }

  def genExpr(code: ASTnode): (Seq[ILOC], String) = {

    /*
    For a binary operation:
    recursively, generate the code for the left child, note the result register
    recursively, generate the code for the right child, note the result register
    get a fresh register for the result
    generate code that takes the inputs from the registers noted in 1 and 2, performs the operation, and puts the result in the register obtained in 3
    append together the code from 1, 2, and 4.
    return the code from 5 together with the register from 3.
    */

    var ilocSeq: Seq[ILOC] = null
    var register: String = null

    code match {

      //'*'  :  expr -> leftExpr rightExpr
      //'div':  expr -> leftExpr rightExpr
      //'mod':  expr -> leftExpr rightExpr
      //TODO: change leftExpr to be ExprASTnode type, instead of ASTnode as it currently is.
      case multiplicativeExprASTnode(_, operator, leftExpr, rightExpr) => {

        val leftExprCode = genCode(leftExpr)
        val rightExprCode = genCode(rightExpr)

        var ilocSeq: Seq[ILOC] = Seq()
        var iloc: ILOC = null
        var returnRegister = ""
        var leftRegister = ""
        var rightRegister = ""

        // check operator
        if (operator == "*" || operator == "div") {
          /*
           * mult r0 r1 => r2
           * <tr><td align="left">mult</td><td align="left">r0, r_X</td><td align="left">=&gt; r1</td></tr>
           */

          //processExpr(subgraphLeft)
          //processExpr(subgraphRight)
          leftExprCode match {
            case IdentCode(identRegister) => {
              leftRegister = identRegister
            }
            case NumCode(iloc, register) => {

              ilocSeq = ilocSeq :+ iloc
              leftRegister = register

            }
            case BoolCode(iloc, register) => {

            }
            case ExprSeq(ilocArray, register) => {

            }

          }

          rightExprCode match {
            case IdentCode(identRegister) => {
              returnRegister = getFreshRegister()
              ilocSeq :+ new ILOC(opCodeMap(operator) + " " + leftRegister + ", " + identRegister + " => " + returnRegister)
            }
            case NumCode(iloc, register) => {

            }
            case BoolCode(iloc, register) => {

            }
            case ExprSeq(ilocs, register) => {

            }

          }

        } else if (operator == "mod") {

        } else {
          // mark - throw exception
        }

      }
      case _ => {
        throw new codeGenException("WRITEINT expression error: " + code.toString())

      }
    }

    return (ilocSeq, register)

  }

  def main(argv: Array[String]) {

    //START BUILDING UP THIS TEST AST TREE FROM THE SIMPLE PROGRAM BELOW
    //  program
    //    var X as int ;
    //  begin
    //    X := 5 + 2
    //  end

    val source = "X := 5 + 2"

    val ident = identASTnode("source string", "X")
    val num5 = numASTnode("source string", "5")
    val num2 = numASTnode("source string", "2")
    val identNode = declartionASTnode("source string", ident, num5)

    val multiplicative_expr: multiplicativeExprASTnode = multiplicativeExprASTnode(source, "*", num5, num2)
    //    val addExpr : additiveExprASTnode = additiveExprASTnode(source, ADD, term_,  AST_epsilon())
    //    val compare_expr : compareExprASTnode = compareExprASTnode(source, COMP, simple_expr,  AST_epsilon())
    //      val assign = assignmentASTnode(":=", ident, num)
    //      val stmtSeq : statementListASTnode = statementListASTnode(source, assign, AST_epsilon())
    val decls = declarationsListASTnode(source, identNode, AST_epsilon())
    //      val prog = programASTnode(source, decls, stmtSeq)

    //TEST HERE FIRST
    //        genCode(prog, progGraphNode)    

  }

}

// end ilocCodeGenerator
