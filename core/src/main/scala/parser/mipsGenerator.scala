/*
 * typeCheckerTL.scala
 * CS5363-E
 * Spring 2015
 * Amulya Battu developer,tester
 * Gabe Fernandez peer programmer
 * Shravya Gaddam devolper,tester
 * David Holland peer programmer*/

package parser

import java.io._

import parser.ilocCodeGeneratorTL._

import scala.collection.mutable.Seq

object mipsGeneratorTL {

  var writerMIPS: PrintWriter = null

  def setFileName(fileName: String) {
    writerMIPS = new PrintWriter(new File(fileName))
  }

  def main(argv: Array[String]) {
    var blockMap: Map[String, Seq[ILOC]] = Map()
    /*  blockMap = ("B1" -> new Array["first", "secondIloc"])
    blockMap += ("B2" -> new Array["firstIloc", "secondIloc"])
    mipsCode = generateMIPS(blockMap);

    Map[String, Seq[ILOC]] = 
     {
        "B1":["loadI 0 => r_X", "loadI 0 => r_Y"],
        "B2":["exit"]
     }*/
  }

  case class Program(val codeMap: scala.collection.mutable.Map[String, Seq[ILOC]]) {
    override def toString = "\tli $fp, 0x7ffffffc\n%s".format(codeMap.map(c => c.toString).mkString)
  }

  val base = 0x7ffffffc //base addr for virtual registers in the memory map

  val onlyDigitsRegex = "^\\d*$".r

  def isAllDigits(x: String) = x match {
    case onlyDigitsRegex() => true
    case _ => false
  }


  //def offset(r: String): String = {  //returns virtual register offset as a Hex string
  def offset(r: String): String = {
    //returns virtual register offset as a negative decimal number that is a multiple of 4

    var reg = r.replace("r", "") //strip of leading 'r' to get just number part
    reg = reg.replace(",", "").trim() //remove dangling ','  example:  cmp_LT r2, r3 => r4
    var addr: String = ""

    if (isAllDigits(reg)) {
      //addr =  "0x" + (base - (4 * reg.toInt)).toHexString // stack location of VR
      addr = (-4 * reg.toInt).toString() // stack location of VR
    }
    else {
      //MUST LOOKUP Virtual register in memory map, e.g. r_X
      throw new Exception("Virtual Register allocation error for register: '" + r + "'")

    }

    return addr
  } // end offset

  def genMIPS(blockList: List[(String, Seq[ILOC])]): Seq[String] = {

    // initialize MIPS String

    var mipsSeq = Seq[String](".data\nnewline:\t.asciiz \"\\n\"\n.text\n.globl main\nmain:\nli $fp, 0x7ffffffc\n") //set the frame pointer, which holds high address for all virtual registers
    // register offsets are negative with repect to fp, addressing lower memory at multiples of 4 bytes

    // ILOC ===>  MIP
    for ((blockLabel, ilocSequence) <- blockList) {

      // Add blockLabel
      mipsSeq = mipsSeq :+ (blockLabel + ":\n")

      for (iloc <- ilocSequence) {

        val IlocInstruction = iloc.ilocValue.replace(",", "")
        val code = IlocInstruction.split(" ")

        code(0) match {

          case "loadI" => {
            //example:   loadI 2 r1
            //loadI c1, r1 => li $t0, c1
            //                sw $t0, Ox($fp)      where 'Ox' is some offset number in Hex or decimal

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val c1 = code(1)
            val li = "li $t0, " + c1
            mipsSeq = mipsSeq :+ li

            val r3_offset = offset(code(3))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "cmp_EQ" => {
            //cmp_EQ r1,r2 r3 =>  lw $t0, Ox($fp)
            //                    lw $t1, Ox($fp)
            //                    seq t0, $t0, $t1
            //                    sw $t0", Ox($fp)    where 'Ox' is some offset number in Hex or decimal

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "seq $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "cmp_LT" => {
            //cmp_LT => lw $t0,  Ox($fp)
            //          lw $t1,  Ox($fp)
            //          slt $t0", $t0", $t1,
            //          sw $t0,  Ox($fp)            where 'Ox' is some offset number in Hex or decimal 

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "slt $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "cmp_GT" => {
            //cmp_GT => lw $t0, offset(r1))($fp)
            //lw $t1", offset(r2))($fp)
            //sgt $t0, $t0, $t1
            //sw $t0, offset(r3))($fp)

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "sgt $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "cmp_LE" => {
            //cmp_LE => lw $t0,  Ox($fp)
            //          lw $t1,  Ox($fp)
            //          sle $t0, $t0, $t1
            //          sw $t0,  Ox($fp)

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "sle $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "cmp_GE" => {
            //cmp_GE => lw $t0, offset(r1))
            //lw $t1, offset(r2))
            //sge $t0, $t0, $t1
            //sw $t0, offset(r3)))

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "sge $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "mult" => {
            //mult => lw $t1,  Ox($fp)
            //        lw $t2,  Ox($fp)
            //        mul $t0, $t1, $t2
            //        sw $t0,  Ox($fp)          where 'Ox' is some offset number in Hex or decimal

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t1, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t2, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "mul $t0, $t1, $t2"

            val r0_offset = offset(code(4))
            val sw = "sw $t0, " + r0_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "add" => {
            //add => lw $t0, Ox($fp)
            //       lw $t1, Ox($fp)
            //       add $t0 , $t0, $t1
            //       sw $t0, Ox($fp)    where 'Ox' is some offset number in Hex or decimal

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "add $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "sub" => {
            //sub => lw $t0, Ox($fp)
            //       lw $t1, Ox($fp)
            //       sub $t0, $t0, $t1
            //       sw $t0, Ox($fp)       where 'Ox' is some offset number in Hex or decimal for some virtual register

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "subu $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "div" => {
            //div => lw t0, offset(r1)($fp)
            //      lw $t1, offset(r2)($fp)
            //      div $t0, $t0, $t1
            //      sw $t0, offset(r3)($fp)

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            val r2_offset = offset(code(2))
            lw = "lw $t1, " + r2_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "div $t0, $t0, $t1"

            val r3_offset = offset(code(4))
            val sw = "sw $t0, " + r3_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "i2i" => {
            //i2 r1, r2 => lw $t1, Ox($fp)    //offset for r1
            //               add $t0", "$t1, $zero
            //               sw $t0, Ox($fp)    //offset for r2

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t1, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "add $t0, $t1, $zero"

            val r2_offset = offset(code(3))
            val sw = "sw $t0, " + r2_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "writeInt" => {
            //writeInt => li v0", 1
            //            lw $t0 , Ox($fp)
            //            add $a0, $t0, $zero
            //            call()
            //            li $v0, 4)
            //            la $a0, newline
            //            call()

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            var li = "li $v0, " + 1
            mipsSeq = mipsSeq :+ li

            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            //mipsSeq = mipsSeq :+ "add $a0, $t1 $zero"
            mipsSeq = mipsSeq :+ "add $a0, $t0 $zero"
            mipsSeq = mipsSeq :+ "syscall"
            li = "li $v0, " + 4
            mipsSeq = mipsSeq :+ li

            var la = "la $a0,  newline"
            mipsSeq = mipsSeq :+ la
            mipsSeq = mipsSeq :+ "syscall\n"

          }
          case "readInt" => {
            //readInt => li("$v0", 5)
            //           syscall()
            //           add("$t0", "$v0", "$zero")
            //           sw("$t0", offset(r1)))

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            var li = "li $v0, " + 5
            mipsSeq = mipsSeq :+ li
            mipsSeq = mipsSeq :+ "syscall"
            mipsSeq = mipsSeq :+ "add $t0, $v0, $zero"

            val r1_offset = offset(code(2))
            val sw = "sw $t0, " + r1_offset + "($fp)\n"
            mipsSeq = mipsSeq :+ sw

          }
          case "exit" => {
            //exit => li $v0, 10
            //        syscall

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            var li = "li $v0, " + 10
            mipsSeq = mipsSeq :+ li
            mipsSeq = mipsSeq :+ "syscall\n"

          }

          case "cbr" => {
            // cbr => lw $t0, Ox($fp)
            //        bne $t0, $zero, b2     //b2 is some label to jump to
            //        j b3                   //be is some lable to jump to

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val r1_offset = offset(code(1))
            var lw = "lw $t0, " + r1_offset + "($fp)"
            mipsSeq = mipsSeq :+ lw

            mipsSeq = mipsSeq :+ "bne $t0, $zero, " + code(3)

            val jump = "j " + code(4) + "\n"
            mipsSeq = mipsSeq :+ jump

          }

          case "jumpI" => {
            // jumpI => j b1       //b1 is some label to jump to

            mipsSeq = mipsSeq :+ ("# " + IlocInstruction)
            val j = "j " + code(2) + "\n"
            mipsSeq = mipsSeq :+ j

          }

          case _ => {
            throw new Exception("UNKNOWN iloc instruction error, " + code(0))
          }

        } // end match
      } // end inner for
    } // end for

    for (line <- mipsSeq) {
      //      println(line) //write to console
      writerMIPS.write(line + "\n") //write to file
    }

    writerMIPS.flush()
    writerMIPS.close()

    return mipsSeq

  } // end genMips

}

// end mipsGeneratorT



