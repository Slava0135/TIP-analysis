package tip.analysis

import tip.ast.AstNodeData.DeclarationData
import tip.ast._
import tip.cfg._
import tip.lattices._
import tip.solvers._

abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(true) {

  val lattice: MapLattice[CfgNode, PowersetLattice[AAssignStmt]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element = {
    n match {
      case _: CfgFunEntryNode => lattice.sublattice.bottom
      case stmt: CfgStmtNode =>
        stmt.data match {
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier => removedefs(s, Seq(id)) + as
              case _ => ???
            }
          case _ => s
        }
      case _ => s
    }
  }

  def removedefs(s: lattice.sublattice.Element, x: Seq[AIdentifier]): lattice.sublattice.Element = {
    val decls = x.map(declData(_))
    s.filterNot { as =>
      as.left match {
        case id: AIdentifier => decls.contains(declData(id))
        case _ => ???
      }
    }
  }

}

/**
 * Live variables analysis that uses the simple fixpoint solver.
 */
class ReachingDefAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

/**
 * Live variables analysis that uses the worklist solver.
 */
class ReachingDefAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
  extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies

