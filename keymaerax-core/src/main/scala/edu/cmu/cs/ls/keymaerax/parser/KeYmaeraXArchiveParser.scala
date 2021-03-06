/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core.Expression

/**
  * Splits a KeYmaera X archive into its parts and forwards to respective problem/tactic parsers. An archive contains
  * at least one entry combining a model in the .kyx format and a (partial) proof tactic in .kyt format.
  *
  * Format example:
  * {{{
  *   ArchiveEntry "Entry 1".
  *     Functions. ... End.
  *     ProgramVariables. ... End.
  *     Problem. ... End.
  *     Tactic "Proof 1". ... End.
  *     Tactic "Proof 2". ... End.
  *   End.
  *   ArchiveEntry "Entry 2". ... End.
  * }}}
  *
  * Created by smitsch on 12/29/16.
  */
object KeYmaeraXArchiveParser {
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntry"
  private val LEMMA_BEGIN: String = "Lemma"
  private val THEOREM_BEGIN: String = "Theorem"
  private val TACTIC_BEGIN: String = "Tactic"
  private val EXERCISE_BEGIN: String = "Exercise"
  private val DEFINITIONS_BEGIN: String = "SharedDefinitions."
  private val END_BLOCK: String = "End."

  /** Two groups: entry name, model+optional tactic */
  private val NAME_REGEX = "^\"([^\"]*)\"\\.(?s)(.*)".r

  private val INFO_REGEX = "(?m)^\\s*(\\w+)\\s*\"([^\"]*)\"\\.\\s*$".r("name", "info")

  /** The entry name, kyx file content (model), parsed model, and parsed name+tactic. */
  case class ParsedArchiveEntry(name: String, kind: String, fileContent: String,
                                defs: KeYmaeraXProblemParser.Declaration,
                                model: Expression, tactics: List[(String, BelleExpr)],
                                info: Map[String, String])
  /** The entry name, kyx file content, entry kind (theorem, lemma, etc.), a list of name+tactic text, and named info. */
  type ArchiveEntry = (String, String, String, List[(String, String)], Map[String, String])

  /** Reads all (file.kyx) or a specific archive entry (file.kyx#entry) from said `file`. */
  def apply(file: String): List[ParsedArchiveEntry] = {
    file.split('#').toList match {
      case fileName :: Nil =>
        val input = scala.io.Source.fromFile(fileName).mkString
        KeYmaeraXArchiveParser.parse(input)
      case fileName :: entryName :: Nil =>
        val input = scala.io.Source.fromFile(fileName).mkString
        KeYmaeraXArchiveParser.getEntry(entryName, input).
          getOrElse(throw new IllegalArgumentException("Unknown archive entry " + entryName)) :: Nil
    }
  }

  /** Parses the archive content into archive entries with parsed model and tactics. */
  def parse(archiveContentBOM: String): List[ParsedArchiveEntry] = {
    val archiveContents: List[ArchiveEntry] = read(archiveContentBOM)
    archiveContents.map(parseEntry)
  }

  /** Reads a specific entry from the archive. */
  def getEntry(entryName: String, archiveContentBOM: String): Option[ParsedArchiveEntry] = {
    val archiveContents: List[ArchiveEntry] = read(archiveContentBOM)
    archiveContents.find(_._1 == entryName).map(parseEntry)
  }

  /** Parses an entry (model and tactic). */
  private def parseEntry(entry: ArchiveEntry): ParsedArchiveEntry = {
    val (name, modelText, kind, tactics, info) = entry
    val (defs, formula) = KeYmaeraXProblemParser.parseProblem(modelText)
    val parsedTactics = tactics.map({
      case (tacticName, tacticText) => (tacticName, BelleParser.parseWithInvGen(tacticText, None, defs)) })
    ParsedArchiveEntry(name, kind, modelText, defs, formula, parsedTactics, info)
  }

  /** Reads the archive content into string-only archive entries. */
  def read(archiveContentBOM: String): List[ArchiveEntry] = {
    val archiveContent: String = ParserHelper.removeBOM(archiveContentBOM)
    // match the word boundary before ArchiveEntry etc. followed by "Name".
    val regex = (s"(?s)\\b(?=$DEFINITIONS_BEGIN)|\\b(?=($ARCHIVE_ENTRY_BEGIN|$LEMMA_BEGIN|$THEOREM_BEGIN|$EXERCISE_BEGIN)" +
      "(?=(\\W*)\"([^\"]*)\"\\.(.*)$))").r

    var globalDefs: Option[String] = None

    regex.split(archiveContent.trim()).filter(_.nonEmpty).flatMap({s =>
      val (entry, kind) =
        if (s.startsWith(DEFINITIONS_BEGIN)) (s.stripPrefix(DEFINITIONS_BEGIN), "definitions")
        else if (s.startsWith(ARCHIVE_ENTRY_BEGIN)) (s.stripPrefix(ARCHIVE_ENTRY_BEGIN), "theorem")
        else if (s.startsWith(THEOREM_BEGIN)) (s.stripPrefix(THEOREM_BEGIN), "theorem")
        else if (s.startsWith(LEMMA_BEGIN)) (s.stripPrefix(LEMMA_BEGIN), "lemma")
        else if (s.startsWith(EXERCISE_BEGIN)) (s.stripPrefix(EXERCISE_BEGIN), "exercise")
        else try {
          KeYmaeraXProblemParser(s)
          (s, "model")
        } catch {
          case e: Throwable =>
            throw new IllegalArgumentException(
              s"""Archive with multiple entries should contain either
                 |    $DEFINITIONS_BEGIN, $ARCHIVE_ENTRY_BEGIN, $LEMMA_BEGIN, $THEOREM_BEGIN,
                 |but got unknown entry
                 |$s
                 |
                 |Fallback to parsing as stand-alone entry failed as well""".stripMargin, e)
        }

        kind match {
          case "model" =>
            val (model, tactics, info) = parseContent(s)
            ("Unnamed", model, "theorem", tactics, info)::Nil
          case "definitions" =>
            globalDefs = Some(entry.trim().stripSuffix(END_BLOCK).trim())
            Nil
          case _ =>
            NAME_REGEX.findAllMatchIn(entry.trim().stripSuffix(END_BLOCK)).map({ m =>
              val modelName = m.group(1)
              val (model: String, tactics: List[(String, String)], info: Map[String, String]) = parseContent(m.group(2))
              //@note copies shared definitions into each Functions/Definitions block.
              val augmentedModel = globalDefs match {
                case Some(d) if model.contains("Functions.") || model.contains("Definitions.") =>
                  "(Functions\\.)|(Definitions\\.)".r.replaceFirstIn(model,
                    "Definitions.\n" + d.replaceAllLiterally("\\", "\\\\") + "\n")
                case Some(d) if !(model.contains("Functions.") || model.contains("Definitions.")) =>
                  "Definitions.\n" + d + "\nEnd.\n" + model
                case None => model
              }
              (modelName, augmentedModel, kind, tactics, info)
            })
        }
    }).toList
  }

  /** Splits content into a model, tactics, and info. */
  private def parseContent(content: String) = {
    content.split(TACTIC_BEGIN).toList match {
      case modelContent :: ts =>
        val info = INFO_REGEX.findAllMatchIn(modelContent.trim()).map({
          tm => (tm.group("name"), tm.group("info"))
        }).toMap
        val modelText = INFO_REGEX.replaceAllIn(modelContent, "").trim()
        (modelText,
          ts.flatMap(tacticText => {
            NAME_REGEX.findAllMatchIn(tacticText.trim().stripSuffix(END_BLOCK)).map({
              tm => (tm.group(1), tm.group(2))
            })
          }),
          info)
    }
  }
}
