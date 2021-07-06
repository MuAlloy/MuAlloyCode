/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;

import org.alloytools.alloy.core.AlloyCore;

import alloyfl.himualloy.util.TestRunner;
import aunit.coverage.AlloyParagraph;
import aunit.coverage.Construct;
import aunit.coverage.CoverageCriteriaBuilder;
import aunit.coverage.Formula;
import aunit.coverage.FunctionInvocation;
import aunit.coverage.RelMultiplicity;
import aunit.coverage.SigAbstract;
import aunit.coverage.SigParagraph;
import aunit.coverage.Signature;
import aunit.coverage.TestCase;
import aunit.gui.AUnitExecution;
import aunit.gui.AUnitTreeNode;
import aunit.gui.CommandFactFormulaNode;
import aunit.gui.CommandFormulaNode;
import aunit.gui.CommandHeaderNode;
import aunit.gui.CoverageInformation;
import aunit.gui.CoverageLeafNode;
import aunit.gui.CoverageTreeNode;
import aunit.gui.FuncCallHolder;
import aunit.gui.MuAlloyHeaderNode;
import aunit.gui.MuAlloyTreeNode;
import aunit.gui.PassFailTreeNode;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstMap;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.MailBug;
import edu.mit.csail.sdg.alloy4.OurDialog;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.Version;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerTask;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4viz.StaticInstanceReader;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Decl;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.ExprHasName;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Func;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.ast.Test;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.A4SolutionWriter;
import edu.mit.csail.sdg.translator.Simplifier;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.ast.BinaryExpression;
import kodkod.engine.CapacityExceededException;
import kodkod.engine.fol2sat.HigherOrderDeclException;
import mualloy.opt.MutantGeneratorOpt;
import mualloy.util.AUnitTestCase;
import mualloy.visitor.ModelMutator;
import parser.ast.nodes.ModelUnit;
import parser.etc.Names;
import parser.util.AlloyUtil;
import parser.util.FileUtil;
import parser.util.StringUtil;

/** This helper method is used by SimpleGUI. */

@SuppressWarnings("restriction" )
final class SimpleReporter extends A4Reporter {

    public static final class SimpleCallback1 implements WorkerCallback {

        private final SimpleGUI                   gui;
        private final VizGUI                      viz;
        private final SwingLogPanel               span;
        private final Set<ErrorWarning>           warnings = new HashSet<ErrorWarning>();
        private final List<String>                results  = new ArrayList<String>();
        private int                               len2     = 0, len3 = 0, verbosity = 0;
        private final String                      latestName;
        private final int                         latestVersion;

        //Variables for printing and storing AUnit results
        private ArrayList<JTree>                  aunitTrees;
        private HashMap<String,ArrayList<JTree>>  coverageTrees;
        private ArrayList<String>                 coverageOrder;
        private ArrayList<CoverageInformation>    covInfos;
        private ArrayList<DefaultMutableTreeNode> cmdNodes;

        //Variables for printing and storing MuAlloy results
        private ArrayList<JTree>                  mualloyTrees;


        public SimpleCallback1(SimpleGUI gui, VizGUI viz, SwingLogPanel span, int verbosity, String latestName, int latestVersion) {
            this.gui = gui;
            this.viz = viz;
            this.span = span;
            this.verbosity = verbosity;
            this.latestName = latestName;
            this.latestVersion = latestVersion;
            len2 = len3 = span.getLength();

            aunitTrees = new ArrayList<JTree>();
            coverageTrees = new HashMap<String,ArrayList<JTree>>();
            coverageOrder = new ArrayList<String>();
            covInfos = new ArrayList<CoverageInformation>();
            cmdNodes = new ArrayList<DefaultMutableTreeNode>();

            mualloyTrees = new ArrayList<JTree>();

        }

        @Override
        public void done() {
            if (viz != null)
                span.setLength(len2);
            else
                span.logDivider();
            span.flush();
            gui.doStop(0);
        }

        @Override
        public void fail() {
            span.logBold("\nAn error has occurred!\n");
            span.logDivider();
            span.flush();
            gui.doStop(1);
        }

        @Override
        public void callback(Object msg) {
            if (msg == null) {
                span.logBold("Done\n");
                span.flush();
                return;
            }
            if (msg instanceof String) {
                span.logBold(((String) msg).trim() + "\n");
                span.flush();
                return;
            }
            if (msg instanceof Throwable) {
                for (Throwable ex = (Throwable) msg; ex != null; ex = ex.getCause()) {
                    if (ex instanceof OutOfMemoryError) {
                        span.logBold("\nFatal Error: the solver ran out of memory!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase memory under the Options menu.\n");
                        return;
                    }
                    if (ex instanceof StackOverflowError) {
                        span.logBold("\nFatal Error: the solver ran out of stack space!\n" + "Try simplifying your model or reducing the scope,\n" + "or increase stack under the Options menu.\n");
                        return;
                    }
                }
            }
            if (msg instanceof Err) {
                Err ex = (Err) msg;
                String text = "fatal";
                boolean fatal = false;
                if (ex instanceof ErrorSyntax)
                    text = "syntax";
                else if (ex instanceof ErrorType)
                    text = "type";
                else
                    fatal = true;
                if (ex.pos == Pos.UNKNOWN)
                    span.logBold("A " + text + " error has occurred:  ");
                else
                    span.logLink("A " + text + " error has occurred:  ", "POS: " + ex.pos.x + " " + ex.pos.y + " " + ex.pos.x2 + " " + ex.pos.y2 + " " + ex.pos.filename);
                if (verbosity > 2) {
                    span.log("(see the ");
                    span.logLink("stacktrace", "MSG: " + ex.dump());
                    span.log(")\n");
                } else {
                    span.log("\n");
                }
                span.logIndented(ex.msg.trim());
                span.log("\n");
                if (fatal && latestVersion > Version.buildNumber())
                    span.logBold("\nNote: You are running Alloy build#" + Version.buildNumber() + ",\nbut the most recent is Alloy build#" + latestVersion + ":\n( version " + latestName + " )\nPlease try to upgrade to the newest version," + "\nas the problem may have been fixed already.\n");
                span.flush();
                if (!fatal)
                    gui.doVisualize("POS: " + ex.pos.x + " " + ex.pos.y + " " + ex.pos.x2 + " " + ex.pos.y2 + " " + ex.pos.filename);
                return;
            }
            if (msg instanceof Throwable) {
                Throwable ex = (Throwable) msg;
                span.logBold(ex.toString().trim() + "\n");
                span.flush();
                return;
            }
            if (!(msg instanceof Object[]))
                return;
            Object[] array = (Object[]) msg;
            if (array[0].equals("pop")) {
                span.setLength(len2);
                String x = (String) (array[1]);
                if (viz != null && x.length() > 0)
                    OurDialog.alert(x);
            }
            if (array[0].equals("declare")) {
                gui.doSetLatest((String) (array[1]));
            }
            if (array[0].equals("S2")) {
                len3 = len2 = span.getLength();
                span.logBold("" + array[1]);
            }
            if (array[0].equals("R3")) {
                span.setLength(len3);
                span.log("" + array[1]);
            }
            if (array[0].equals("link")) {
                span.logLink((String) (array[1]), (String) (array[2]));
            }
            if (array[0].equals("bold")) {
                span.logBold("" + array[1]);
            }
            if (array[0].equals("")) {
                span.log("" + array[1]);
            }
            if (array[0].equals("scope") && verbosity > 0) {
                span.log("   " + array[1]);
            }
            if (array[0].equals("bound") && verbosity > 1) {
                span.log("   " + array[1]);
            }
            if (array[0].equals("resultCNF")) {
                results.add(null);
                span.setLength(len3);
                span.log("   File written to " + array[1] + "\n\n");
            }
            if (array[0].equals("highlight")) {
                gui.doVisualize("COV");
            }
            if (array[0].equals("coverage")) {
                span.logBold("" + array[1]);
            }
            if (array[0].equals("startResults")) {
                //Initialize for AUnit displays
                gui.doDisplayAUnitStart();
            }
            if (array[0].equals("summaryResults")) {
                //Send information for the summary results bar for AUnit
                gui.doDisplaySummaryBar((Integer) array[1], (Integer) array[2], (Integer) array[3], (String) array[4], (Integer) array[5]);
            }
            if (array[0].equals("addResult")) {
                //Add an AUnit test result
                DefaultMutableTreeNode cmnHeader = new DefaultMutableTreeNode(new CommandHeaderNode("Command:"));
                cmdNodes.add(cmnHeader);
                boolean no_cmd = true;
                boolean no_facts = false;

                //Command node - display any invoked formulas for AUnit and the facts of the model
                if (((String) array[3]).length() > 0) {
                    cmnHeader.add(new DefaultMutableTreeNode(new CommandFormulaNode((String) array[3])));
                    no_cmd = false;
                }
                String[] facts = ((String) array[6]).split("\n");
                if (facts[0].equals("")) {
                    no_facts = true;
                } else {
                    DefaultMutableTreeNode factNodes = new DefaultMutableTreeNode(new CommandFormulaNode("Facts of the model:"));
                    for (int i = 0; i < facts.length; i++) {
                        factNodes.add(new DefaultMutableTreeNode(new CommandFactFormulaNode(facts[i])));
                    }
                    cmnHeader.add(factNodes);
                }
                //Catch if there is no contraints to add
                if (no_cmd && no_facts) {
                    cmnHeader.add(new DefaultMutableTreeNode(new CommandFormulaNode("true")));
                }

                //Create the necessary result JTree node to display based on the AUnit test result
                if (((String) array[2]).contains("passes")) {
                    DefaultMutableTreeNode newResult = new DefaultMutableTreeNode(new PassFailTreeNode("pass", array[1] + " " + array[2]));
                    newResult.add(new DefaultMutableTreeNode(new AUnitTreeNode("Valuation", "" + array[4], array[1] + "")));
                    newResult.add(cmnHeader);
                    aunitTrees.add(new JTree(newResult));
                } else if (((String) array[2]).contains("fails")) {
                    DefaultMutableTreeNode newResult = new DefaultMutableTreeNode(new PassFailTreeNode("fail", array[1] + " " + array[2]));
                    newResult.add(new DefaultMutableTreeNode(new AUnitTreeNode("Valuation", "" + array[4], array[1] + "")));
                    newResult.add(cmnHeader);
                    aunitTrees.add(new JTree(newResult));
                } else {
                    DefaultMutableTreeNode newResult = new DefaultMutableTreeNode(new PassFailTreeNode("error", array[1] + " " + array[2]));
                    newResult.add(new DefaultMutableTreeNode(new AUnitTreeNode("Valuation", "" + array[4], array[1] + "")));
                    newResult.add(cmnHeader);
                    aunitTrees.add(new JTree(newResult));
                }
            }
            if (array[0].equals("finishTree")) {
                //Wrap up and display all the AUnit results in the AUnit tab
                gui.doDisplayAUnitTree(aunitTrees, cmdNodes);
            }
            if (array[0].equals("finishCoverageTree")) {
                //If displaying coverage, send invocation to update the coverage tab
                gui.doDisplayCoverageTable(covInfos, cov_per_test);
            }
            if (array[0].equals("addCoverageNode")) {
                //Generate information for coverage of each coverage criteria
                String[] split = array[1].toString().split("::-::");
                String paragraph_name = split[0];

                //Store coverage information based on the Alloy paragrapg it belongs to
                CoverageInformation covInfo = new CoverageInformation(paragraph_name);
                coverageOrder.add(paragraph_name);
                coverageTrees.put(paragraph_name, new ArrayList<JTree>());

                //Build up and nest trees for coverae as needed
                DefaultMutableTreeNode current = null;
                DefaultMutableTreeNode tree = null;
                int totalCriteria = 0;
                int numCovered = 0;
                for (int i = 1; i < split.length; i++) {
                    String color = "";
                    String[] get_content = split[i].split(":-:");

                    if (get_content[0].equals("criteria")) {
                        String coverage_of_criteria = get_content[2];
                        if (coverage_of_criteria.equals("covered")) {
                            color = "green";
                        } else if (coverage_of_criteria.equals("not")) {
                            color = "red";
                        } else {
                            color = "yellow";
                        }

                        if (current != null) {
                            coverageTrees.get(paragraph_name).add(new JTree(current));
                        }
                        current = new DefaultMutableTreeNode(new CoverageTreeNode(color, get_content[1], get_content[3], Integer.valueOf(get_content[4]), Integer.valueOf(get_content[5])));
                        tree = new DefaultMutableTreeNode(new CoverageTreeNode(color, get_content[1], get_content[3], Integer.valueOf(get_content[4]), Integer.valueOf(get_content[5])));
                        covInfo.add(get_content[1], new JTree(tree));
                    } else if (get_content[0].equals("node")) {
                        String coverage_of_criteria = get_content[2];
                        if (coverage_of_criteria.equals("true")) {
                            totalCriteria++;
                            numCovered++;
                            color = "green";
                        } else {
                            totalCriteria++;
                            color = "red";
                        }

                        tree.add(new DefaultMutableTreeNode(new CoverageLeafNode(color, get_content[1])));
                        current.add(new DefaultMutableTreeNode(new CoverageLeafNode(color, get_content[1])));
                    }
                }
                covInfo.totalCriteria = totalCriteria;
                covInfo.covered = numCovered;
                covInfos.add(covInfo);
                coverageTrees.get(paragraph_name).add(new JTree(current));
            }
            if (array[0].equals("addMuAlloyTestSummary")) {
                //Send information to the main display for mualloy summary
                gui.doDisplaySummaryMuAlloyTest((Integer) array[1], (Integer) array[2], (long) array[3], (long) array[4], (long) array[5], (String) array[6]);
            }
            if (array[0].equals("addNonKilledMutant")) {
                //Add a mutation result for non-killed mutants
                //Contains information outlining the non-killed mutant and a mutation killing test case
                DefaultMutableTreeNode newResult = new DefaultMutableTreeNode(new MuAlloyHeaderNode((String) array[1]));
                newResult.add(new DefaultMutableTreeNode(new MuAlloyTreeNode((String) array[1], (String) array[2], (String) array[3], (String) array[4], (String) array[5])));
                mualloyTrees.add(new JTree(newResult));
            }
            if (array[0].equals("finishMutation")) {
                //Send information to the main display to generate the mualloy result tab
                gui.doDisplayMuAlloy(mualloyTrees);
            }

            if (array[0].equals("debug") && verbosity > 2) {
                span.log("   " + array[1] + "\n");
                len2 = len3 = span.getLength();
            }
            if (array[0].equals("translate")) {
                span.log("   " + array[1]);
                len3 = span.getLength();
                span.logBold("   Generating CNF...\n");
            }
            if (array[0].equals("solve")) {
                span.setLength(len3);
                span.log("   " + array[1]);
                len3 = span.getLength();
                span.logBold("   Solving...\n");
            }
            if (array[0].equals("warnings")) {
                if (warnings.size() == 0)
                    span.setLength(len2);
                else if (warnings.size() > 1)
                    span.logBold("Note: There were " + warnings.size() + " compilation warnings. Please scroll up to see them.\n\n");
                else
                    span.logBold("Note: There was 1 compilation warning. Please scroll up to see them.\n\n");
                if (warnings.size() > 0 && Boolean.FALSE.equals(array[1])) {
                    Pos e = warnings.iterator().next().pos;
                    gui.doVisualize("POS: " + e.x + " " + e.y + " " + e.x2 + " " + e.y2 + " " + e.filename);
                    span.logBold("Warnings often indicate errors in the model.\n" + "Some warnings can affect the soundness of the analysis.\n" + "To proceed despite the warnings, go to the Options menu.\n");
                }
            }
            if (array[0].equals("warning")) {
                ErrorWarning e = (ErrorWarning) (array[1]);
                if (!warnings.add(e))
                    return;
                Pos p = e.pos;
                span.logLink("Warning #" + warnings.size(), "POS: " + p.x + " " + p.y + " " + p.x2 + " " + p.y2 + " " + p.filename);
                span.log("\n");
                span.logIndented(e.msg.trim());
                span.log("\n\n");
            }
            if (array[0].equals("sat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String filename = (String) (array[3]), formula = (String) (array[4]);
                results.add(filename);
                (new File(filename)).deleteOnExit();
                gui.doSetLatest(filename);
                span.setLength(len3);
                span.log("   ");
                span.logLink(chk ? "Counterexample" : "Instance", "XML: " + filename);
                span.log(" found. ");
                span.logLink(chk ? "Assertion" : "Predicate", formula);
                span.log(chk ? " is invalid" : " is consistent");
                if (expects == 0)
                    span.log(", contrary to expectation");
                else if (expects == 1)
                    span.log(", as expected");
                span.log(". " + array[5] + "ms.\n\n");
                gui.doDisplayRun();
            }
            if (array[0].equals("metamodel")) {
                String outf = (String) (array[1]);
                span.setLength(len2);
                (new File(outf)).deleteOnExit();
                gui.doSetLatest(outf);
                span.logLink("Metamodel", "XML: " + outf);
                span.log(" successfully generated.\n\n");
            }
            if (array[0].equals("minimizing")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                span.setLength(len3);
                span.log(chk ? "   No counterexample found." : "   No instance found.");
                if (chk)
                    span.log(" Assertion may be valid");
                else
                    span.log(" Predicate may be inconsistent");
                if (expects == 1)
                    span.log(", contrary to expectation");
                else if (expects == 0)
                    span.log(", as expected");
                span.log(". " + array[4] + "ms.\n");
                span.logBold("   Minimizing the unsat core of " + array[3] + " entries...\n");
            }
            if (array[0].equals("unsat")) {
                boolean chk = Boolean.TRUE.equals(array[1]);
                int expects = (Integer) (array[2]);
                String formula = (String) (array[4]);
                span.setLength(len3);
                span.log(chk ? "   No counterexample found. " : "   No instance found. ");
                span.logLink(chk ? "Assertion" : "Predicate", formula);
                span.log(chk ? " may be valid" : " may be inconsistent");
                gui.doDisplayRun();
                if (expects == 1)
                    span.log(", contrary to expectation");
                else if (expects == 0)
                    span.log(", as expected");
                if (array.length == 5) {
                    span.log(". " + array[3] + "ms.\n\n");
                    span.flush();
                    return;
                }
                String core = (String) (array[5]);
                int mbefore = (Integer) (array[6]), mafter = (Integer) (array[7]);
                span.log(". " + array[3] + "ms.\n");
                if (core.length() == 0) {
                    results.add("");
                    span.log("   No unsat core is available in this case. " + array[8] + "ms.\n\n");
                    span.flush();
                    return;
                }
                results.add(core);
                (new File(core)).deleteOnExit();
                span.log("   ");
                span.logLink("Core", core);
                if (mbefore <= mafter)
                    span.log(" contains " + mafter + " top-level formulas. " + array[8] + "ms.\n\n");
                else
                    span.log(" reduced from " + mbefore + " to " + mafter + " top-level formulas. " + array[8] + "ms.\n\n");
            }
            span.flush();
        }
    }

    private void cb(Serializable... objs) {
        cb.callback(objs);
    }

    /** {@inheritDoc} */
    @Override
    public void resultCNF(final String filename) {
        cb("resultCNF", filename);
    }

    /** {@inheritDoc} */
    @Override
    public void warning(final ErrorWarning ex) {
        warn++;
        cb("warning", ex);
    }

    /** {@inheritDoc} */
    @Override
    public void scope(final String msg) {
        cb("scope", msg);
    }

    /** {@inheritDoc} */
    @Override
    public void bound(final String msg) {
        cb("bound", msg);
    }

    /** {@inheritDoc} */
    @Override
    public void debug(final String msg) {
        cb("debug", msg.trim());
    }

    /** {@inheritDoc} */
    @Override
    public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
        lastTime = System.currentTimeMillis();
        if (aunit_extension_executions) {
            //Currently no details to track
        } else {
            cb("translate", "Solver=" + solver + " Bitwidth=" + bitwidth + " MaxSeq=" + maxseq + (skolemDepth == 0 ? "" : " SkolemDepth=" + skolemDepth) + " Symmetry=" + (symmetry > 0 ? ("" + symmetry) : "OFF") + '\n');
        }
    }

    /** {@inheritDoc} */
    @Override
    public void solve(final int primaryVars, final int totalVars, final int clauses) {
        if (aunit_extension_executions) {
            //No details saved currently
        } else {
            cb("solve", "" + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses. " + (System.currentTimeMillis() - lastTime) + "ms.\n");
        }
        lastTime = System.currentTimeMillis();
    }

    /** {@inheritDoc} */
    @Override
    public void resultSAT(Object command, long solvingTime, Object solution) {
        if (!(solution instanceof A4Solution) || !(command instanceof Command))
            return;
        A4Solution sol = (A4Solution) solution;
        Command cmd = (Command) command;
        String formula = recordKodkod ? sol.debugExtractKInput() : "";
        String filename = tempfile + ".xml";
        synchronized (SimpleReporter.class) {
            try {
                if (!aunit_extension_executions)
                    cb("R3", "   Writing the XML file...");
                if (latestModule != null)
                    writeXML(this, latestModule, filename, sol, latestKodkodSRC);
            } catch (Throwable ex) {
                cb("bold", "\n" + (ex.toString().trim()) + "\nStackTrace:\n" + (MailBug.dump(ex).trim()) + "\n");
                return;
            }
            latestKodkods.clear();
            latestKodkods.add(sol.toString());
            latestKodkod = sol;
            latestKodkodXML = filename;
        }
        String formulafilename = "";
        if (formula.length() > 0 && tempfile != null) {
            formulafilename = tempfile + ".java";
            try {
                Util.writeAll(formulafilename, formula);
                formulafilename = "CNF: " + formulafilename;
            } catch (Throwable ex) {
                formulafilename = "";
            }
        }
        if (aunit_extension_executions) {
            String details = System.currentTimeMillis() - lastTime + "ms";
            aunitTestDetails.add(details);
        } else {
            cb("sat", cmd.check, cmd.expects, filename, formulafilename, System.currentTimeMillis() - lastTime);
        }
    }

    /** {@inheritDoc} */
    @Override
    public void minimizing(Object command, int before) {
        if (!(command instanceof Command))
            return;
        Command cmd = (Command) command;
        minimized = System.currentTimeMillis();
        cb("minimizing", cmd.check, cmd.expects, before, minimized - lastTime);
    }

    /** {@inheritDoc} */
    @Override
    public void minimized(Object command, int before, int after) {
        minimizedBefore = before;
        minimizedAfter = after;
    }

    /** {@inheritDoc} */
    @Override
    public void resultUNSAT(Object command, long solvingTime, Object solution) {
        if (!(solution instanceof A4Solution) || !(command instanceof Command))
            return;
        A4Solution sol = (A4Solution) solution;
        Command cmd = (Command) command;
        String originalFormula = recordKodkod ? sol.debugExtractKInput() : "";
        String corefilename = "", formulafilename = "";
        if (originalFormula.length() > 0 && tempfile != null) {
            formulafilename = tempfile + ".java";
            try {
                Util.writeAll(formulafilename, originalFormula);
                formulafilename = "CNF: " + formulafilename;
            } catch (Throwable ex) {
                formulafilename = "";
            }
        }
        Pair<Set<Pos>,Set<Pos>> core = sol.highLevelCore();
        if ((core.a.size() > 0 || core.b.size() > 0) && tempfile != null) {
            corefilename = tempfile + ".core";
            OutputStream fs = null;
            ObjectOutputStream os = null;
            try {
                fs = new FileOutputStream(corefilename);
                os = new ObjectOutputStream(fs);
                os.writeObject(core);
                os.writeObject(sol.lowLevelCore());
                corefilename = "CORE: " + corefilename;
            } catch (Throwable ex) {
                corefilename = "";
            } finally {
                Util.close(os);
                Util.close(fs);
            }
        }
        if (aunit_extension_executions) {
            String details = System.currentTimeMillis() - lastTime + "ms";
            aunitTestDetails.add(details);
        } else {
            if (minimized == 0)
                cb("unsat", cmd.check, cmd.expects, (System.currentTimeMillis() - lastTime), formulafilename);
            else
                cb("unsat", cmd.check, cmd.expects, minimized - lastTime, formulafilename, corefilename, minimizedBefore, minimizedAfter, (System.currentTimeMillis() - minimized));
        }
    }

    private final WorkerCallback cb;

    // ========== These fields should be set each time we execute a set of
    // commands

    /** Whether we should record Kodkod input/output. */
    private final boolean recordKodkod;

    /**
     * The time that the last action began; we subtract it from
     * System.currentTimeMillis() to determine the elapsed time.
     */
    private long          lastTime  = 0;

    /**
     * If we performed unsat core minimization, then this is the start of the
     * minimization, else this is 0.
     */
    private long          minimized = 0;

    /** The unsat core size before minimization. */
    private int           minimizedBefore;

    /** The unsat core size after minimization. */
    private int           minimizedAfter;

    /**
     * The filename where we can write a temporary Java file or Core file.
     */
    private String        tempfile  = null;

    // ========== These fields may be altered as each successful command
    // generates a Kodkod or Metamodel instance

    /**
     * The set of Strings already enumerated for this current solution.
     */
    private static final Set<String>        latestKodkods              = new LinkedHashSet<String>();

    /**
     * The A4Solution corresponding to the latest solution generated by Kodkod; this
     * field must be synchronized.
     */
    private static A4Solution               latestKodkod               = null;

    /**
     * The root Module corresponding to this.latestKodkod; this field must be
     * synchronized.
     */
    private static Module                   latestModule               = null;

    /**
     * The source code corresponding to the latest solution generated by Kodkod;
     * this field must be synchronized.
     */
    private static ConstMap<String,String>  latestKodkodSRC            = null;

    /**
     * The XML filename corresponding to the latest solution generated by Kodkod;
     * this field must be synchronized.
     */
    private static String                   latestKodkodXML            = null;

    /**
     * The XML filename corresponding to the latest metamodel generated by
     * TranslateAlloyToMetamodel; this field must be synchronized.
     */
    private static String                   latestMetamodelXML         = null;

    //Track details for aunit tests
    static ArrayList<String>                aunitTestDetails           = new ArrayList<String>();
    //boolean flag to indicate aunit or one of its extensions is executing which changes logging information
    static boolean                          aunit_extension_executions = false;
    public static ArrayList<FuncCallHolder> func_calls_per_test;
    static HashMap<String,JTree>            cov_per_test               = new HashMap<String,JTree>();

    /** Constructor is private. */
    private SimpleReporter(WorkerCallback cb, boolean recordKodkod) {
        this.cb = cb;
        this.recordKodkod = recordKodkod;
    }

    /** Helper method to write out a full XML file. */
    private static void writeXML(A4Reporter rep, Module mod, String filename, A4Solution sol, Map<String,String> sources) throws Exception {
        sol.writeXML(rep, filename, mod.getAllFunc(), sources);
        if (AlloyCore.isDebug())
            validate(filename);
    }

    private int warn = 0;

    /** Task that performs solution enumeration. */
    public static final class SimpleTask2 implements WorkerTask {

        private static final long       serialVersionUID = 0;
        public String                   filename         = "";
        public transient WorkerCallback out              = null;

        private void cb(Object... objs) throws Exception {
            out.callback(objs);
        }

        @Override
        public void run(WorkerCallback out) throws Exception {
            this.out = out;
            cb("S2", "Enumerating...\n");
            A4Solution sol;
            Module mod;
            synchronized (SimpleReporter.class) {
                if (latestMetamodelXML != null && latestMetamodelXML.equals(filename)) {
                    cb("pop", "You cannot enumerate a metamodel.\n");
                    return;
                }
                if (latestKodkodXML == null || !latestKodkodXML.equals(filename)) {
                    cb("pop", "You can only enumerate the solutions of the most-recently-solved command.");
                    return;
                }
                if (latestKodkod == null || latestModule == null || latestKodkodSRC == null) {
                    cb("pop", "Error: the SAT solver that generated the instance has exited,\nso we cannot enumerate unless you re-solve that command.\n");
                    return;
                }
                sol = latestKodkod;
                mod = latestModule;
            }
            if (!sol.satisfiable()) {
                cb("pop", "Error: This command is unsatisfiable,\nso there are no solutions to enumerate.");
                return;
            }
            if (!sol.isIncremental()) {
                cb("pop", "Error: This solution was not generated by an incremental SAT solver.\n" + "Currently only MiniSat and SAT4J are supported.");
                return;
            }
            int tries = 0;
            while (true) {
                sol = sol.next();
                if (!sol.satisfiable()) {
                    cb("pop", "There are no more satisfying instances.\n\n" + "Note: due to symmetry breaking and other optimizations,\n" + "some equivalent solutions may have been omitted.");
                    return;
                }
                String toString = sol.toString();
                synchronized (SimpleReporter.class) {
                    if (!latestKodkods.add(toString))
                        if (tries < 100) {
                            tries++;
                            continue;
                        }
                    // The counter is needed to avoid a Kodkod bug where
                    // sometimes we might repeat the same solution infinitely
                    // number of times; this at least allows the user to keep
                    // going
                    writeXML(null, mod, filename, sol, latestKodkodSRC);
                    latestKodkod = sol;
                }
                cb("declare", filename);
                return;
            }
        }
    }

    /**
     * Validate the given filename to see if it is a valid Alloy XML instance file.
     */
    private static void validate(String filename) throws Exception {
        A4SolutionReader.read(new ArrayList<Sig>(), new XMLNode(new File(filename))).toString();
        StaticInstanceReader.parseInstance(new File(filename));
    }

    /** Task that perform one command. */
    public static final class SimpleTask1 implements WorkerTask {

        private static final long serialVersionUID = 0;
        public A4Options          options;
        public String             tempdir;
        public boolean            bundleWarningNonFatal;
        public int                bundleIndex;
        public int                resolutionMode;
        public Map<String,String> map;

        public SimpleTask1() {
        }

        public void cb(WorkerCallback out, Object... objs) throws IOException {
            out.callback(objs);
        }

        @Override
        public void run(WorkerCallback out) throws Exception {
            cb(out, "S2", "Starting the solver...\n\n");
            final SimpleReporter rep = new SimpleReporter(out, options.recordKodkod);
            final Module world = CompUtil.parseEverything_fromFile(rep, map, options.originalFilename, resolutionMode);
            final List<Sig> sigs = world.getAllReachableSigs();
            final ConstList<Command> cmds = world.getAllCommands();
            cb(out, "warnings", bundleWarningNonFatal);
            if (rep.warn > 0 && !bundleWarningNonFatal)
                return;
            List<String> result = new ArrayList<String>(cmds.size());
            if (bundleIndex == -2) {
                final String outf = tempdir + File.separatorChar + "m.xml";
                cb(out, "S2", "Generating the metamodel...\n");
                PrintWriter of = new PrintWriter(outf, "UTF-8");
                Util.encodeXMLs(of, "\n<alloy builddate=\"", Version.buildDate(), "\">\n\n");
                A4SolutionWriter.writeMetamodel(ConstList.make(sigs), options.originalFilename, of);
                Util.encodeXMLs(of, "\n</alloy>");
                Util.close(of);
                if (AlloyCore.isDebug())
                    validate(outf);
                cb(out, "metamodel", outf);
                synchronized (SimpleReporter.class) {
                    latestMetamodelXML = outf;
                }
            } else
                for (int i = 0; i < cmds.size(); i++)
                    if (bundleIndex < 0 || i == bundleIndex) {
                        synchronized (SimpleReporter.class) {
                            latestModule = world;
                            latestKodkodSRC = ConstMap.make(map);
                        }
                        final String tempXML = tempdir + File.separatorChar + i + ".cnf.xml";
                        final String tempCNF = tempdir + File.separatorChar + i + ".cnf";
                        final Command cmd = cmds.get(i);
                        rep.tempfile = tempCNF;
                        cb(out, "bold", "Executing \"" + cmd + "\"\n");
                        A4Solution ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), cmd, options);
                        if (ai == null)
                            result.add(null);
                        else if (ai.satisfiable())
                            result.add(tempXML);
                        else if (ai.highLevelCore().a.size() > 0)
                            result.add(tempCNF + ".core");
                        else
                            result.add("");
                    }
            (new File(tempdir)).delete(); // In case it was UNSAT, or
                                         // canceled...
            if (result.size() > 1) {
                rep.cb("bold", "" + result.size() + " commands were executed. The results are:\n");
                for (int i = 0; i < result.size(); i++) {
                    Command r = world.getAllCommands().get(i);
                    if (result.get(i) == null) {
                        rep.cb("", "   #" + (i + 1) + ": Unknown.\n");
                        continue;
                    }
                    if (result.get(i).endsWith(".xml")) {
                        rep.cb("", "   #" + (i + 1) + ": ");
                        rep.cb("link", r.check ? "Counterexample found. " : "Instance found. ", "XML: " + result.get(i));
                        rep.cb("", r.label + (r.check ? " is invalid" : " is consistent"));
                        if (r.expects == 0)
                            rep.cb("", ", contrary to expectation");
                        else if (r.expects == 1)
                            rep.cb("", ", as expected");
                    } else if (result.get(i).endsWith(".core")) {
                        rep.cb("", "   #" + (i + 1) + ": ");
                        rep.cb("link", r.check ? "No counterexample found. " : "No instance found. ", "CORE: " + result.get(i));
                        rep.cb("", r.label + (r.check ? " may be valid" : " may be inconsistent"));
                        if (r.expects == 1)
                            rep.cb("", ", contrary to expectation");
                        else if (r.expects == 0)
                            rep.cb("", ", as expected");
                    } else {
                        if (r.check)
                            rep.cb("", "   #" + (i + 1) + ": No counterexample found. " + r.label + " may be valid");
                        else
                            rep.cb("", "   #" + (i + 1) + ": No instance found. " + r.label + " may be inconsistent");
                        if (r.expects == 1)
                            rep.cb("", ", contrary to expectation");
                        else if (r.expects == 0)
                            rep.cb("", ", as expected");
                    }
                    rep.cb("", ".\n");
                }
                rep.cb("", "\n");
            }
            if (rep.warn > 1)
                rep.cb("bold", "Note: There were " + rep.warn + " compilation warnings. Please scroll up to see them.\n");
            if (rep.warn == 1)
                rep.cb("bold", "Note: There was 1 compilation warning. Please scroll up to see it.\n");
        }
    }

    /** Task that perform aunit test execution and coverage calculations. */
    static final class AunitExecutionTask implements WorkerTask {

        private static final long serialVersionUID = 0;
        public A4Options          options;
        public String             tempdir;
        public boolean            bundleWarningNonFatal;
        public int                bundleIndex;
        public int                resolutionMode;
        public Map<String,String> map;
        public boolean            coverage;
        public boolean            highlight;

        enum Outcome {
                      PASSING,
                      FAILING,
                      ERROR
        }

        ArrayList<Expr> exprs_in_command = new ArrayList<Expr>();

        public AunitExecutionTask() {
        }

        public void cb(WorkerCallback out, Object... objs) throws IOException {
            out.callback(objs);
        }

        @SuppressWarnings("resource" )

        public void run(WorkerCallback out) throws Exception {
            cb(out, "S2", "Starting the solver...\n\n");
            final SimpleReporter rep = new SimpleReporter(out, options.recordKodkod);
            CompModule world = CompUtil.parseEverything_fromFile(rep, map, options.originalFilename, resolutionMode);
            cb(out, "warnings", bundleWarningNonFatal);
            if (rep.warn > 0 && !bundleWarningNonFatal)
                return;

            aunitTestDetails.clear();
            aunit_extension_executions = true;
            func_calls_per_test = new ArrayList<FuncCallHolder>();
            int totalTime = 0;

            /**
             * Create the different model versions to enable easy (1) testing, (2) coverage
             * calculations
             **/
            String temporig = "";
            for (String s : map.keySet()) {
                if (s.equals(options.originalFilename)) {
                    temporig = map.get(s);
                    break;
                }
            }
            String[] model_vers = AUnitExecution.buildModelVersions(world, temporig, options);

            /**
             * Create the easy-printing Alloy model and parse the file into a Module object
             * (world)
             **/
            PrintWriter writer = new PrintWriter("executableOriginal.als", "UTF-8");
            writer.println(model_vers[1]);
            writer.close();
            world = CompUtil.parseEverything_fromFile(rep, map, "executableOriginal.als", resolutionMode);

            /**
             * Create the module without any facts of the model for coverage calculations
             * and displaying of any valuation
             **/
            writer = new PrintWriter("removedFacts.als", "UTF-8");
            writer.println(model_vers[0]);
            writer.close();
            CompModule worldRemovedFacts = CompUtil.parseEverything_fromFile(rep, map, "removedFacts.als", resolutionMode);

            /* Helper storage for executing tasks, display results */
            /** Store the result from executing any tests **/
            ArrayList<Outcome> results = new ArrayList<Outcome>();
            /** Map the unique test label to the associated test case **/
            HashMap<String,TestCase> aunit_tests = new HashMap<String,TestCase>();
            /**
             * A mapping of the name of the parameters for each function in the alloy model
             * under test
             **/
            HashMap<String,ArrayList<String>> func_to_parameters = new HashMap<String,ArrayList<String>>();
            /** Array of all tests in the Model Under Test **/
            Test[] parsed_tests = new Test[world.getAllTests().size()];
            parsed_tests = world.getAllTests().toArray(parsed_tests);
            HashMap<String,Func> name_to_func = new HashMap<String,Func>();
            HashSet<String> preds = new HashSet<String>();
            HashSet<String> vals = new HashSet<String>();

            /** Populate func_to_parameters mapping **/
            for (Func func : world.getAllFunc()) {
                String func_name = func.label.toString(); //isolate the name of the function invoked
                func_name = func_name.substring(func_name.indexOf("/") + 1);
                if (!func_name.contains("run$") && !func_name.contains("check$")) { //Check that the function is not a command 
                    func_to_parameters.put(func_name, new ArrayList<String>());
                    AUnitExecution.addDomains(func.getBody(), new HashMap<String,String>());
                    if (func.decls.size() > 0) { //Add the name of the parameters to the mapping i.e. Acyclic[l: List] maps as Acyclic->l
                        for (Decl parameter : func.decls) {
                            for (ExprHasName var : parameter.names) {
                                func_to_parameters.get(func_name).add(var.toString());
                            }
                        }
                    }
                    if (!func.isVal) {
                        preds.add(func_name);
                    } else {
                        vals.add(func_name);
                    }
                }
                name_to_func.put(func_name, func);
            }

            AUnitExecution.addDomains(world.getAllReachableFacts(), new HashMap<String,String>());
            /** Map the name of the function to the other functions it calls **/
            HashMap<String,ArrayList<FunctionInvocation>> func_to_calls = AUnitExecution.buildCalledMap(world, func_to_parameters, name_to_func);

            /** Start to piece together (1) valuation and (2) commands for AUnit tests **/
            cb(out, "bold", "Parsing " + parsed_tests.length + " AUnit tests\n");
            HashSet<Expr> sig_fact_exprs = new HashSet<Expr>();
            /**
             * Get the invoked commands starting with the valuations which call commands
             * with parameters within them.
             **/
            for (int i = 0; i < parsed_tests.length; i++) {
                TestCase testcase = new TestCase();
                /**
                 * Set up the predicate(s) invoked by the command - this is needed for coverage
                 * to know which predicates to look over for coverage.
                 **/
                AUnitExecution.resetExplicitCalls();

                if (parsed_tests[i].getUnresolvedTestCmd().formula instanceof ExprVar && (!((ExprVar) parsed_tests[i].getUnresolvedTestCmd().formula).label.contains("run$")) && (!((ExprVar) parsed_tests[i].getUnresolvedTestCmd().formula).label.contains("check$"))) { //directly invoked a function that has no parameters
                    String func_name = ((ExprVar) parsed_tests[i].getUnresolvedTestCmd().formula).label;

                    Func pontenial_val = name_to_func.get(func_name);
                    if (!pontenial_val.isVal) {
                        aunit_extension_executions = false;
                        cb(out, "error", "AUnit Execution Error: Test \"" + parsed_tests[i].id + "\" does not reference a valuation.\n\n", parsed_tests[i].getTestCmd().pos);
                        /** Clean up files the get created **/
                        File delete_creations = new File("executableOriginal.als");
                        delete_creations.delete();
                        delete_creations = new File("removedFacts.als");
                        delete_creations.delete();
                        return;
                    }
                    for (FunctionInvocation func_invocation : func_to_calls.get(func_name)) {
                        testcase.addExplicitCall(func_invocation);
                    }
                    parsed_tests[i].setValuation(pontenial_val);
                } else {
                    AUnitExecution.findExplicitCalls(parsed_tests[i].getTestCmd().formula, func_to_parameters, new HashMap<String,String>());
                    for (FunctionInvocation func_call : AUnitExecution.getExplicitCalls()) {
                        if (!func_call.isVal) {
                            testcase.addExplicitCall(func_call);
                        }
                        for (FunctionInvocation func_invocation : func_to_calls.get(func_call.getCommand())) {
                            testcase.addExplicitCall(func_invocation);
                        }
                    }

                    /**
                     * Report an error if (1) no valuation in the test or (2) more than one
                     * valuation in the test.
                     **/

                    if (!parsed_tests[i].establishValuation(world)) {
                        if (parsed_tests[i].getValuationFunc() != null)
                            cb(out, "error", "AUnit Execution Error: Test \"" + parsed_tests[i].id + "\" references more than one valuation.\n\n", parsed_tests[i].getTestCmd().pos);
                        else
                            cb(out, "error", "AUnit Execution Error: Test \"" + parsed_tests[i].id + "\" does not reference a valuation.\n\n", parsed_tests[i].getTestCmd().pos);
                        aunit_extension_executions = false;

                        /** Clean up files the get created **/
                        File delete_creations = new File("executableOriginal.als");
                        delete_creations.delete();
                        delete_creations = new File("removedFacts.als");
                        delete_creations.delete();
                        return;
                    }
                }
                parsed_tests[i].establishCommand(world, model_vers[2].split("\n"), preds);

                AUnitExecution.resetExplicitCalls();
                AUnitExecution.findExplicitCalls(world.getAllReachableFacts(), func_to_parameters, new HashMap<String,String>());
                for (FunctionInvocation func_call : AUnitExecution.getExplicitCalls()) {
                    if (!func_call.isVal) {
                        testcase.addExplicitCall(func_call);
                    }
                    for (FunctionInvocation func_invocation : func_to_calls.get(func_call.getCommand())) {
                        testcase.addExplicitCall(func_invocation);
                    }
                }

                for (Sig sig : world.getAllReachableSigs()) {
                    for (Expr sig_fact : sig.getFacts()) {
                        AUnitExecution.resetExplicitCalls();
                        AUnitExecution.findExplicitCalls(sig_fact, func_to_parameters, new HashMap<String,String>());
                        for (FunctionInvocation func_call : AUnitExecution.getExplicitCalls()) {
                            if (!func_call.isVal) {
                                sig_fact_exprs.add(func_call.exprCall);
                            }
                            for (FunctionInvocation func_invocation : func_to_calls.get(func_call.getCommand())) {
                                sig_fact_exprs.add(func_invocation.exprCall);
                            }
                        }
                    }
                }
                testcase.removeRecursiveCalls(sig_fact_exprs);
                aunit_tests.put(parsed_tests[i].id, testcase);
            }

            /** Execute all AUnit Tests **/
            if (coverage) {
                cb(out, "bold", "Executing AUnit tests and calculating coverage\n");
            } else {
                cb(out, "bold", "Executing AUnit tests\n");
            }

            /** If calculating coverage, find all criteria in the model under test. **/

            CoverageCriteriaBuilder ccb = null;
            ccb = new CoverageCriteriaBuilder(world);
            ccb.findCriteria(model_vers[2]);
            if (coverage) {
                //  cb(out, "", ccb.printCoverageString());
            }
            String facts = "";
            for (SigParagraph sigP : ccb.getSigParagraphs()) {
                for (Construct fact : sigP.getImplicitFacts()) {
                    if (fact instanceof SigAbstract) {
                        SigAbstract formula = (SigAbstract) fact;
                        facts += formula.prettyPrintName + "\n";
                    } else if (fact instanceof RelMultiplicity) {
                        RelMultiplicity formula = (RelMultiplicity) fact;
                        facts += formula.prettyPrintName + "\n";
                    } else if (fact instanceof Formula) {
                        Formula formula = (Formula) fact;
                        facts += formula.prettyPrintName + "\n";
                    }
                }
            }

            for (String origin : ccb.getParagraphs().keySet()) {
                if (origin.contains("fact ")) {
                    facts += origin + "\n";
                } else if (origin.contains("facts")) {
                    facts += "Unamed fact paragraph(s)\n";
                }
            }


            /**
             * Loop over all previously located tests. For each test: a. Build up storage
             * areas for the results b. Build a command that adds in the facts of the model
             * along with the valuation and test case command c. Execute this command and
             * store the results d. Calculate coverage along the way, if necessary
             **/
            int numPassing = 0;
            int numFailing = 0;
            int numErrors = 0;

            for (int i = 0; i < parsed_tests.length; i++) {
                synchronized (SimpleReporter.class) {
                    latestModule = world;
                    latestKodkodSRC = ConstMap.make(map);
                }
                final String tempXML = tempdir + File.separatorChar + i + ".cnf.xml";
                final String tempCNF = tempdir + File.separatorChar + i + ".cnf";
                final Command cmd = parsed_tests[i].getTestCmd();

                rep.tempfile = tempCNF;
                cb(out, "", "     Executing \"" + cmd + "\"\n");

                /* Execute test */
                Command test_with_facts = new Command(cmd.check, cmd.overall, cmd.bitwidth, cmd.maxseq, cmd.formula.and(world.getAllReachableFacts()));
                TranslateAlloyToKodkod k = new TranslateAlloyToKodkod(rep, options, world.getAllReachableSigs(), test_with_facts);
                k.makeFacts(test_with_facts.formula);
                A4Solution ai = null;
                try {
                    ai = k.frame.solve(rep, cmd, new Simplifier(), true);
                } catch (UnsatisfiedLinkError ex) {
                    throw new ErrorFatal("The required JNI library cannot be found: " + ex.toString().trim(), ex);
                } catch (CapacityExceededException ex) {
                    throw ex;
                } catch (HigherOrderDeclException ex) {
                    Pos p = k.frame.kv2typepos(ex.decl().variable()).b;
                    throw new ErrorType(p, "Analysis cannot be performed since it requires higher-order quantification that could not be skolemized.");
                } catch (Throwable ex) {
                    if (ex instanceof Err)
                        throw (Err) ex;
                    else
                        throw new ErrorFatal("Unknown exception occurred: " + ex, ex);
                }
                /*
                 * Store result, and calculate number of passing, failing or erroring producing
                 * tests
                 */
                if (ai == null) {
                    results.add(Outcome.ERROR);
                    numErrors++;
                    aunitTestDetails.add("");
                } else if (ai.satisfiable()) {
                    if (cmd.expects == 0) {
                        results.add(Outcome.FAILING);
                        numFailing++;
                    } else if (cmd.expects == 1) {
                        results.add(Outcome.PASSING);
                        numPassing++;
                    } else {
                        if (cmd.check) {
                            results.add(Outcome.FAILING);
                            numFailing++;
                        } else {
                            results.add(Outcome.PASSING);
                            numPassing++;
                        }
                    }
                } else {
                    if (cmd.expects == 1) {
                        results.add(Outcome.FAILING);
                        numFailing++;
                    } else if (cmd.expects == 0) {
                        results.add(Outcome.PASSING);
                        numPassing++;
                    } else {
                        if (!cmd.check) {
                            results.add(Outcome.FAILING);
                            numFailing++;
                        } else {
                            results.add(Outcome.PASSING);
                            numPassing++;
                        }
                    }
                }

                /* Set valuation for storage, and calculate coverage if needed */
                Expr valuation = CompUtil.parseOneExpression_fromString(world, parsed_tests[i].prettyPrintValuation());
                Command getValuation = new Command(cmd.check, cmd.overall, cmd.bitwidth, cmd.maxseq, valuation.and(world.getAllReachableFacts()));
                ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), getValuation, options);
                FuncCallHolder func_calls = new FuncCallHolder(i);

                boolean add = true;
                for (int c = 0; c < k.calls.size(); c++) {
                    String f_call_params = "";
                    String comma = "";
                    if (!sig_fact_exprs.contains(k.calls.get(c).exprCall)) {
                        for (int j = 0; j < k.calls.get(c).parameters.size(); j++) {
                            if (k.calls.get(c).parameters.get(j) instanceof kodkod.ast.Relation) {
                                f_call_params += comma + k.calls.get(c).parameters.get(j).toString();
                                aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), k.calls.get(c).parameters.get(j).toString());
                            } else if (k.calls.get(c).parameters.get(j) instanceof kodkod.ast.Variable) {
                                String param = k.calls.get(c).parameters.get(j).toString();
                                if (param.contains("_")) {
                                    String is_val = param.substring(0, param.indexOf("_"));
                                    if (vals.contains(is_val)) {
                                        String var = param.substring(param.indexOf("_") + 1);
                                        f_call_params += comma + var;
                                        aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), "$" + var);
                                    } else if (preds.contains(is_val)) {
                                        f_call_params += comma + param;
                                        String domain = aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).outerdomains.get(param.substring(param.indexOf("_") + 1));
                                        aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), " : " + domain + " | ");
                                    } else {
                                        f_call_params += comma + param;
                                        aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), "$" + param);
                                    }
                                } else if (aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).outerdomains.containsKey(param)) {
                                    f_call_params += comma + param;
                                    String domain = aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).outerdomains.get(param);
                                    aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), " : " + domain + " | ");

                                } else {
                                    f_call_params += comma + param;
                                    aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), "$" + param);
                                }
                            } else if (k.calls.get(c).parameters.get(j) instanceof kodkod.ast.BinaryExpression) {
                                String param = buildExp((BinaryExpression) k.calls.get(c).parameters.get(j));
                                if (param.contains(" remainder")) { //extended sig directly called
                                    param = param.substring(param.indexOf("+") + 1, param.indexOf(" remainder"));
                                    param = param.substring(param.indexOf("/") + 1);
                                    aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), param);

                                } else {
                                    f_call_params += comma + param;
                                    aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).updateParameter(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getParameterOrder().get(j), param);
                                }
                            }
                            comma = ", ";
                        }
                        if (add)
                            func_calls.addExplicitCall(aunit_tests.get(parsed_tests[i].id).eCommands.get(k.calls.get(c).exprCall).getCommand() + "[" + f_call_params.replaceAll("\\$", "") + "]");
                        add = true;
                    }
                }

                func_calls_per_test.add(func_calls);
                if (!ai.satisfiable()) {
                    valuation = CompUtil.parseOneExpression_fromString(worldRemovedFacts, parsed_tests[i].prettyPrintValuation());
                    getValuation = new Command(cmd.check, cmd.overall, cmd.bitwidth, cmd.maxseq, valuation);
                    ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, worldRemovedFacts.getAllReachableSigs(), getValuation, options);
                    if (coverage) {
                        ccb.world = worldRemovedFacts;
                        ccb.markCoverage(ai, aunit_tests.get(parsed_tests[i].id));
                    }
                } else {
                    if (coverage) {
                        ccb.world = world;
                        ccb.markCoverage(ai, aunit_tests.get(parsed_tests[i].id));
                    }
                }
                /* Store valuation */
                aunit_tests.get(parsed_tests[i].id).setValuationXML(tempXML);
            }

            /** Start displaying coverage results **/
            if (coverage) {
                rep.cb("startCoverageTree", world.getModelName());
                String coverage_string = "";
                String coverage_color = "";
                String covfilename = "model.cov";
                OutputStream fs = null;
                ObjectOutputStream os = null;
                fs = new FileOutputStream(covfilename);
                os = new ObjectOutputStream(fs);

                for (SigParagraph sigP : ccb.getSigParagraphs()) {
                    Signature sig = sigP.getSig();
                    Pos temp = sig.getAlloySig().pos;
                    Pos sigPos = new Pos(options.originalFilename, temp.x - 4, temp.y, temp.x + sig.label.length() - 1, 0);
                    os.writeObject(sigPos);

                    coverage_string = "Signature " + sig.label + "::-::";
                    if (sig.isCovered()) {
                        coverage_string += "criteria:-:sig " + sig.label + ":-:covered:-:" + sigPos.y + ":-:" + sigPos.y2 + ":-:" + sig.getNumCovered() + ":-:" + sig.getNumCriteria() + "::-::";
                        coverage_color = "green";
                    } else if (sig.noCoverage()) {
                        coverage_string += "criteria:-:sig " + sig.label + ":-:not:-:" + sigPos.y + ":-:" + sigPos.y2 + ":-:" + sig.getNumCovered() + ":-:" + sig.getNumCriteria() + "::-::";
                        coverage_color = "red";
                    } else {
                        coverage_string += "criteria:-:sig " + sig.label + ":-:partial:-:" + sigPos.y + ":-:" + sigPos.y2 + ":-:" + sig.getNumCovered() + ":-:" + sig.getNumCriteria() + "::-::";
                        coverage_color = "yellow";
                    }
                    os.writeObject(coverage_color);

                    for (String criteria : sig.getPrettyPrintOrder()) {
                        if (sig.getCurrentCoverage().get(criteria) == Construct.Coverage.COVERED) {
                            coverage_string += "node:-:" + criteria + ":-:" + "true::-::";
                        } else {
                            coverage_string += "node:-:" + criteria + ":-:" + "false::-::";
                        }
                    }

                    for (aunit.coverage.Relation rel : sigP.getRelations()) {
                        Pos oldPos = rel.getAlloyRelation().pos;
                        Pos newPos = new Pos(options.originalFilename, oldPos.x, oldPos.y, oldPos.x2, oldPos.y2);
                        os.writeObject(newPos);
                        if (rel.isCovered()) {
                            coverage_string += "criteria:-:" + rel.label + ":-:covered:-:" + newPos.y + ":-:" + newPos.y2 + ":-:" + rel.getNumCovered() + ":-:" + rel.getNumCriteria() + "::-::";
                            coverage_color = "green";
                        } else if (rel.noCoverage()) {
                            coverage_string += "criteria:-:" + rel.label + ":-:not:-:" + newPos.y + ":-:" + newPos.y2 + ":-:" + rel.getNumCovered() + ":-:" + rel.getNumCriteria() + "::-::";
                            coverage_color = "red";
                        } else {
                            coverage_string += "criteria:-:" + rel.label + ":-:partial:-:" + newPos.y + ":-:" + newPos.y2 + ":-:" + rel.getNumCovered() + ":-:" + rel.getNumCriteria() + "::-::";
                            coverage_color = "yellow";
                        }
                        os.writeObject(coverage_color);

                        for (String criteria : rel.getPrettyPrintOrder()) {
                            if (rel.getCurrentCoverage().get(criteria) == Construct.Coverage.COVERED) {
                                coverage_string += "node:-:" + criteria + ":-:" + "true::-::";
                            } else {
                                coverage_string += "node:-:" + criteria + ":-:" + "false::-::";
                            }
                        }
                    }

                    for (Construct fact : sigP.getImplicitFacts()) {
                        Pos newPos = null;
                        if (fact instanceof SigAbstract) {
                            SigAbstract formula = (SigAbstract) fact;
                            Pos oldPos = formula.getAlloySig().isAbstract;
                            newPos = new Pos(options.originalFilename, oldPos.x, oldPos.y, oldPos.x2, oldPos.y2);
                            os.writeObject(newPos);
                        } else if (fact instanceof RelMultiplicity) {
                            RelMultiplicity formula = (RelMultiplicity) fact;
                            Pos oldPos = formula.getAlloyExpr().span();
                            newPos = new Pos(options.originalFilename, oldPos.x, oldPos.y, oldPos.x2, oldPos.y2);
                            os.writeObject(newPos);
                        } else if (fact instanceof Formula) {
                            Formula formula = (Formula) fact;
                            if (formula.pos == null) {
                                Pos oldPos = formula.getAlloyFormula().span();
                                newPos = new Pos(options.originalFilename, oldPos.x, oldPos.y, oldPos.x2, oldPos.y2);
                                os.writeObject(newPos);
                            } else {
                                Pos oldPos = formula.pos;
                                newPos = new Pos(options.originalFilename, oldPos.x, oldPos.y, oldPos.x2, oldPos.y2);
                                os.writeObject(newPos);
                            }
                        }

                        if (fact.isCovered()) {
                            coverage_string += "criteria:-:" + fact.prettyPrintName + ":-:covered:-:" + newPos.y + ":-:" + newPos.y2 + ":-:" + fact.getNumCovered() + ":-:" + fact.getNumCriteria() + "::-::";
                            coverage_color = "green";
                        } else if (fact.noCoverage()) {
                            coverage_string += "criteria:-:" + fact.prettyPrintName + ":-:not:-:" + newPos.y + ":-:" + newPos.y2 + ":-:" + fact.getNumCovered() + ":-:" + fact.getNumCriteria() + "::-::";
                            coverage_color = "red";
                        } else {
                            coverage_string += "criteria:-:" + fact.prettyPrintName + ":-:partial:-:" + newPos.y + ":-:" + newPos.y2 + ":-:" + fact.getNumCovered() + ":-:" + fact.getNumCriteria() + "::-::";
                            coverage_color = "yellow";
                        }

                        for (String criteria : fact.getPrettyPrintOrder()) {
                            if (fact.getCurrentCoverage().get(criteria) == Construct.Coverage.COVERED) {
                                coverage_string += "node:-:" + criteria + ":-:" + "true::-::";
                            } else {
                                coverage_string += "node:-:" + criteria + ":-:" + "false::-::";
                            }
                        }

                        os.writeObject(coverage_color);
                    }
                    rep.cb("addCoverageNode", coverage_string);
                }

                HashMap<String,AlloyParagraph> paragraphs = ccb.getParagraphs();
                for (String origin : paragraphs.keySet()) {
                    coverage_string = origin + "::-::";
                    Pos newPos = null;
                    for (Construct expOrForm : paragraphs.get(origin).getExpressionsAndFormulas()) {
                        if (expOrForm.isCovered()) {
                            coverage_color = "green";
                        } else if (expOrForm.noCoverage()) {
                            coverage_color = "red";
                        } else {
                            coverage_color = "yellow";
                        }

                        if (highlight) {
                            for (Pos highlight : expOrForm.getHighlightPos()) {
                                if (!highlight.filename.equals("")) {
                                    newPos = new Pos(options.originalFilename, highlight.x, highlight.y, highlight.x2, highlight.y2);
                                    os.writeObject(newPos);
                                    os.writeObject(coverage_color);
                                }
                            }
                        }

                        if (expOrForm.isCovered()) {
                            coverage_string += "criteria:-:" + expOrForm.label + ":-:covered:-:" + expOrForm.line_start + ":-:" + expOrForm.getNumCovered() + ":-:" + expOrForm.getNumCriteria() + "::-::";
                            coverage_color = "green";
                        } else if (expOrForm.noCoverage()) {
                            coverage_string += "criteria:-:" + expOrForm.label + ":-:not:-:" + expOrForm.line_start + ":-:" + expOrForm.getNumCovered() + ":-:" + expOrForm.getNumCriteria() + "::-::";
                            coverage_color = "red";
                        } else {
                            coverage_string += "criteria:-:" + expOrForm.label + ":-:partial:-:" + expOrForm.line_start + ":-:" + expOrForm.getNumCovered() + ":-:" + expOrForm.getNumCriteria() + "::-::";
                            coverage_color = "yellow";
                        }

                        for (String criteria : expOrForm.getPrettyPrintOrder()) {
                            if (expOrForm.getCurrentCoverage().get(criteria) == Construct.Coverage.COVERED) {
                                coverage_string += "node:-:" + criteria + ":-:" + "true::-::";
                            } else {
                                coverage_string += "node:-:" + criteria + ":-:" + "false::-::";
                            }
                        }
                    }

                    rep.cb("addCoverageNode", coverage_string);
                }

                rep.cb("finishCoverageTree");
                rep.cb("highlight");
                os.close();
                fs.close();

            }

            if (results.size() > 0) { //at least one test was run
                rep.cb("startResults");

                for (int i = 0; i < results.size(); i++) {
                    String name = " Test: \"" + parsed_tests[i].id + "\" ";
                    String outcome = "";
                    if (results.get(i) == Outcome.ERROR) {
                        outcome = " resulted in an error.";
                    } else if (results.get(i) == Outcome.PASSING) {
                        outcome = " passes. (" + aunitTestDetails.get(i) + ")";
                    } else {
                        outcome = " fails. (" + aunitTestDetails.get(i) + ")";
                    }

                    String timewithMS = aunitTestDetails.get(i);
                    totalTime += Integer.valueOf(timewithMS.substring(0, timewithMS.length() - 2));
                    rep.cb("addResult", name, outcome, parsed_tests[i].prettyPrintCommand(), aunit_tests.get(parsed_tests[i].id).getValuationXML(), func_calls_per_test.get(i).getCallString(), facts);
                }

                String modelName = options.originalFilename.substring(options.originalFilename.lastIndexOf(File.separator) + 1);
                modelName = modelName.substring(0, modelName.indexOf("."));
                rep.cb("summaryResults", numPassing, numFailing, numErrors, modelName, totalTime);
            }

            rep.cb("finishTree");
            if (rep.warn > 1)
                rep.cb("bold", "Note: There were " + rep.warn + " compilation warnings. Please scroll up to see them.\n");
            if (rep.warn == 1)
                rep.cb("bold", "Note: There was 1 compilation warning. Please scroll up to see it.\n");

            /** Clean up and delete files that got created **/
            aunit_extension_executions = false;
            File delete_creations = new File("executableOriginal.als");
            delete_creations.delete();
            delete_creations = new File("removedFacts.als");
            delete_creations.delete();
        }

        private String buildExp(kodkod.ast.Expression exp) {
            String name = "";
            if (exp instanceof kodkod.ast.BinaryExpression) {
                kodkod.ast.BinaryExpression bExp = (kodkod.ast.BinaryExpression) exp;
                return "(" + buildExp(bExp.left()) + " " + bExp.op() + " " + buildExp(bExp.right()) + ")";
            } else if (exp instanceof kodkod.ast.UnaryExpression) {
                kodkod.ast.UnaryExpression uExp = (kodkod.ast.UnaryExpression) exp;
                return uExp.op().toString() + buildExp(uExp.expression());
            } else if (exp instanceof kodkod.ast.Variable) {
                kodkod.ast.Variable var = (kodkod.ast.Variable) exp;
                if (var.toString().contains("_")) {
                    return "$" + var.toString().substring(var.toString().indexOf("_") + 1);
                } else {
                    return "$" + var.toString();
                }
            } else if (exp instanceof kodkod.ast.Relation) {
                kodkod.ast.Relation rel = (kodkod.ast.Relation) exp;
                return rel.toString();
            } else if (exp instanceof kodkod.ast.ConstantExpression) {
                kodkod.ast.ConstantExpression cExp = (kodkod.ast.ConstantExpression) exp;
                return cExp.toString();
            }
            return name;
        }
    }

    /** Task that perform aunit test execution and coverage calculations. */
    static final class MuAlloyExecutionTask implements WorkerTask {

        private static final long serialVersionUID = 0;
        public A4Options          options;
        public String             tempdir;
        public boolean            bundleWarningNonFatal;
        public int                bundleIndex;
        public int                resolutionMode;
        public Map<String,String> map;

        ArrayList<Expr>           exprs_in_command = new ArrayList<Expr>();

        public MuAlloyExecutionTask() {
        }

        public void cb(WorkerCallback out, Object... objs) throws IOException {
            out.callback(objs);
        }

        @SuppressWarnings("resource" )

        public void run(WorkerCallback out) throws Exception {
            cb(out, "S2", "Starting the solver...\n\n");
            final SimpleReporter rep = new SimpleReporter(out, options.recordKodkod);
            CompModule world = CompUtil.parseEverything_fromFile(rep, map, options.originalFilename, resolutionMode);
            cb(out, "warnings", bundleWarningNonFatal);
            if (rep.warn > 0 && !bundleWarningNonFatal)
                return;

            aunitTestDetails.clear();
            aunit_extension_executions = true;
            func_calls_per_test = new ArrayList<FuncCallHolder>();
            int totalTime = 0;

            /**
             * Create the different model versions to enable easy (1) testing, (2) coverage
             * calculations
             **/
            String temporig = "";
            for (String s : map.keySet()) {
                if (s.equals(options.originalFilename)) {
                    temporig = map.get(s);
                    break;
                }
            }

            String modelName = options.originalFilename.substring(options.originalFilename.lastIndexOf(File.separator) + 1);
            modelName = modelName.substring(0, modelName.indexOf("."));

            String[] model_vers = AUnitExecution.buildModelVersions(world, temporig, options);

            PrintWriter writer = new PrintWriter("removedFacts.als", "UTF-8");
            writer.println(model_vers[0]);
            writer.close();
            CompModule worldRemovedFacts = CompUtil.parseEverything_fromFile(rep, map, "removedFacts.als", resolutionMode);


            /** Map the unique test label to the associated test case **/
            HashMap<String,TestCase> aunit_tests = new HashMap<String,TestCase>();
            /**
             * A mapping of the name of the parameters for each function in the alloy model
             * under test
             **/
            HashMap<String,ArrayList<String>> func_to_parameters = new HashMap<String,ArrayList<String>>();
            /** Array of all tests in the Model Under Test **/
            Test[] parsed_tests = new Test[world.getAllTests().size()];
            parsed_tests = world.getAllTests().toArray(parsed_tests);

            HashMap<String,Func> name_to_func = new HashMap<String,Func>();
            HashSet<String> preds = new HashSet<String>();
            HashSet<String> vals = new HashSet<String>();

            /** Populate func_to_parameters mapping **/
            for (Func func : world.getAllFunc()) {
                String func_name = func.label.toString(); //isolate the name of the function invoked
                func_name = func_name.substring(func_name.indexOf("/") + 1);
                if (!func_name.contains("run$") && !func_name.contains("check$")) { //Check that the function is not a command
                    func_to_parameters.put(func_name, new ArrayList<String>());
                    AUnitExecution.addDomains(func.getBody(), new HashMap<String,String>());
                    if (func.decls.size() > 0) { //Add the name of the parameters to the mapping i.e. Acyclic[l: List] maps as Acyclic->l
                        for (Decl parameter : func.decls) {
                            for (ExprHasName var : parameter.names) {
                                func_to_parameters.get(func_name).add(var.toString());
                            }
                        }
                    }
                    if (!func.isVal) {
                        preds.add(func_name);
                    } else {
                        vals.add(func_name);
                    }
                }
                name_to_func.put(func_name, func);
            }

            AUnitExecution.addDomains(world.getAllReachableFacts(), new HashMap<String,String>());
            /** Map the name of the function to the other functions it calls **/
            HashMap<String,ArrayList<FunctionInvocation>> func_to_calls = AUnitExecution.buildCalledMap(world, func_to_parameters, name_to_func);

            /** Start to piece together (1) valuation and (2) commands for AUnit tests **/
            cb(out, "bold", "Parsing " + parsed_tests.length + " AUnit tests\n");
            HashSet<Expr> sig_fact_exprs = new HashSet<Expr>();
            /**
             * Get the invoked commands starting with the valuations which call commands
             * with parameters within them.
             **/
            for (int i = 0; i < parsed_tests.length; i++) {
                TestCase testcase = new TestCase();
                /**
                 * Set up the predicate(s) invoked by the command - this is needed for coverage
                 * to know which predicates to look over for coverage.
                 **/
                AUnitExecution.resetExplicitCalls();

                if (parsed_tests[i].getUnresolvedTestCmd().formula instanceof ExprVar && (!((ExprVar) parsed_tests[i].getUnresolvedTestCmd().formula).label.contains("run$")) && (!((ExprVar) parsed_tests[i].getUnresolvedTestCmd().formula).label.contains("check$"))) { //directly invoked a function that has no parameters
                    String func_name = ((ExprVar) parsed_tests[i].getUnresolvedTestCmd().formula).label;

                    Func pontenial_val = name_to_func.get(func_name);
                    if (!pontenial_val.isVal) {
                        aunit_extension_executions = false;
                        cb(out, "error", "AUnit Execution Error: Test \"" + parsed_tests[i].id + "\" does not reference a valuation.\n\n", parsed_tests[i].getTestCmd().pos);
                        /** Clean up files the get created **/
                        File delete_creations = new File("executableOriginal.als");
                        delete_creations.delete();
                        delete_creations = new File("removedFacts.als");
                        delete_creations.delete();
                        return;
                    }

                    for (FunctionInvocation func_invocation : func_to_calls.get(func_name)) {
                        testcase.addExplicitCall(func_invocation);
                    }
                    parsed_tests[i].setValuation(pontenial_val);
                } else {
                    AUnitExecution.findExplicitCalls(parsed_tests[i].getTestCmd().formula, func_to_parameters, new HashMap<String,String>());
                    for (FunctionInvocation func_call : AUnitExecution.getExplicitCalls()) {
                        if (!func_call.isVal) {
                            testcase.addExplicitCall(func_call);
                        }
                        for (FunctionInvocation func_invocation : func_to_calls.get(func_call.getCommand())) {
                            testcase.addExplicitCall(func_invocation);
                        }
                    }

                    /**
                     * Report an error if (1) no valuation in the test or (2) more than one
                     * valuation in the test.
                     **/

                    if (!parsed_tests[i].establishValuation(world)) {
                        if (parsed_tests[i].getValuationFunc() != null)
                            cb(out, "error", "Test case parsing error: Test \"" + parsed_tests[i].id + "\" references more than one valuation.\n\n", parsed_tests[i].getTestCmd().pos);
                        else
                            cb(out, "error", "Test case parsing error: Test \"" + parsed_tests[i].id + "\" does not reference a valuation.\n\n", parsed_tests[i].getTestCmd().pos);
                        aunit_extension_executions = false;

                        /** Clean up files the get created **/
                        File delete_creations = new File("executableOriginal.als");
                        delete_creations.delete();
                        delete_creations = new File("removedFacts.als");
                        delete_creations.delete();
                        return;
                    }
                }


                parsed_tests[i].establishCommand(world, model_vers[2].split("\n"), preds);

                AUnitExecution.resetExplicitCalls();
                AUnitExecution.findExplicitCalls(world.getAllReachableFacts(), func_to_parameters, new HashMap<String,String>());
                for (FunctionInvocation func_call : AUnitExecution.getExplicitCalls()) {
                    if (!func_call.isVal) {
                        testcase.addExplicitCall(func_call);
                    }
                    for (FunctionInvocation func_invocation : func_to_calls.get(func_call.getCommand())) {
                        testcase.addExplicitCall(func_invocation);
                    }
                }

                for (Sig sig : world.getAllReachableSigs()) {
                    for (Expr sig_fact : sig.getFacts()) {
                        AUnitExecution.resetExplicitCalls();
                        AUnitExecution.findExplicitCalls(sig_fact, func_to_parameters, new HashMap<String,String>());
                        for (FunctionInvocation func_call : AUnitExecution.getExplicitCalls()) {
                            if (!func_call.isVal) {
                                sig_fact_exprs.add(func_call.exprCall);
                            }
                            for (FunctionInvocation func_invocation : func_to_calls.get(func_call.getCommand())) {
                                sig_fact_exprs.add(func_invocation.exprCall);
                            }
                        }
                    }
                }
                testcase.removeRecursiveCalls(sig_fact_exprs);
                aunit_tests.put(parsed_tests[i].id, testcase);
            }

            /** Perform Mutation Testing **/
            cb(out, "bold", "Generating mutants.\n");

            int max_scope = -1;

            //Build up string of all the test in the format mualloy expects
            String test_only_model = "";
            for (Test testcase : parsed_tests) {
                test_only_model += "pred test" + testcase.id + "{\n";
                test_only_model += testcase.prettyPrintValuationWithCmd() + "\n}\n";

                int scope = 3;
                if (testcase.getOrigCmd().overall != -1) {
                    scope = testcase.getOrigCmd().overall;
                    if (testcase.getOrigCmd().overall > max_scope)
                        max_scope = testcase.getOrigCmd().overall;
                }

                if (testcase.getOrigCmd().expects == -1) {
                    test_only_model += "run test" + testcase.id + " for " + scope + " expect 1 \n\n";

                } else {
                    test_only_model += "run test" + testcase.id + " for " + scope + " expect " + testcase.getOrigCmd().expects + "\n\n";
                }
            }

            //No scope specified, used default scope
            if (max_scope == -1) {
                max_scope = 3;
            }

            /**
             * Print Alloy model without tests, and a file with just tests.
             **/

            String model_mutant = AUnitExecution.buildMuAlloyModelVersion(world, temporig, options);
            model_mutant += "\nrun {}";

            writer = new PrintWriter("mutation_model.als", "UTF-8");
            writer.println(model_mutant);
            writer.close();

            writer = new PrintWriter("test_only_model.als", "UTF-8");
            writer.println(test_only_model);
            writer.close();

            String[] mutantGenArgs = new String[6];
            mutantGenArgs[0] = "mutation_model.als";
            mutantGenArgs[1] = "mutation_model.als";
            mutantGenArgs[2] = "mutants";
            mutantGenArgs[3] = "results";
            mutantGenArgs[4] = "meta";

            FileUtil.createDirsIfNotExist(mutantGenArgs[2], mutantGenArgs[3], mutantGenArgs[4]);

            long start_gen = System.nanoTime();
            MutantGeneratorOpt opt = new MutantGeneratorOpt(mutantGenArgs[0], mutantGenArgs[1], mutantGenArgs[2], mutantGenArgs[3], mutantGenArgs[4], max_scope);

            CompModule module = AlloyUtil.compileAlloyModule(opt.getModelPath());
            assert module != null;
            ModelUnit mu = new ModelUnit(null, module);
            // Write pretty printed model to file for easy comparison.
            FileUtil.writeText(mu.accept(opt.getPSV(), null), Paths.get(opt.getMutantDirPath(), Names.ORIGINAL_MODEL_NAME + Names.DOT_ALS).toString(), true);
            // Mutate the model.
            ModelMutator mm = new ModelMutator(opt);
            mu.accept(mm, null);
            StringBuilder testSuite = new StringBuilder();
            int count = 0;

            String test_suite = "";
            ArrayList<String> valuations = new ArrayList<String>();
            ArrayList<String> aunit_valuations = new ArrayList<String>();
            ArrayList<String> aunit_cmds = new ArrayList<String>();
            for (AUnitTestCase testCase : opt.getTests()) {
                test_suite += testCase.toString(count) + "\n\n";
                aunit_valuations.add(testCase.getAUnitFormat(count));
                aunit_cmds.add(testCase.getCommand());
                valuations.add(testCase.getValuation());
                testSuite.append(testCase.toString(count++)).append("\n");
            }

            long end_gen = System.nanoTime();
            cb(out, "bold", "EquivMutantNum: ");
            cb(out, "", String.valueOf(mm.getEquivMutantNum()) + "\n");
            cb(out, "bold", "NonEquivMutantNum: ");
            cb(out, "", String.valueOf(mm.getNonEquivMutantNum()) + "\n");
            cb(out, "bold", "Performing mutation testing.\n");

            long start_mutation = System.nanoTime();
            File dir = new File("mutants");
            File[] mutants = dir.listFiles((d, name) -> name.endsWith(Names.DOT_ALS) && !name.equals(Names.ORIGINAL_MODEL_NAME + Names.DOT_ALS) && !name.equals(Names.MUTATION_BASED_TEST_NAME + Names.DOT_ALS));

            int totalMutantsNum = mutants.length;
            int killedMutantsNum = 0;
            A4Options options = new A4Options();
            options.noOverflow = true;

            HashMap<String,String> mutant_killing_tests = new HashMap<String,String>();
            ArrayList<String> mutant_order = new ArrayList<String>();
            HashMap<String,String> mutant_strings = new HashMap<String,String>();

            for (File mutant : mutants) {
                String mutantAsString = FileUtil.readText(mutant.getAbsolutePath());
                boolean isKilled = !TestRunner.runTestsFailFast(mutantAsString, Paths.get("test_only_model.als").toString(), options);

                if (isKilled) {
                    killedMutantsNum += 1;
                }
                String mutantName = StringUtil.beforeSubstring(mutant.getName(), Names.DOT, true);
                mutant_strings.put(mutantName, mutantAsString);

                //cb(out, "", "Mutant " + mutantName + " is " + (isKilled ? "" : "not ") + "killed.\n");
                if (!isKilled) {
                    String modelAsString = String.join(Names.NEW_LINE, Arrays.asList(mutantAsString, test_suite));
                    FileUtil.writeText(modelAsString, Names.TMPT_FILE_PATH, false);
                    CompModule model = AlloyUtil.compileAlloyModule(Names.TMPT_FILE_PATH);
                    assert model != null;
                    for (Command cmd : model.getAllCommands()) {
                        try {
                            A4Solution ans = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, model.getAllReachableSigs(), cmd, options);
                            int actual = ans.satisfiable() ? 1 : 0;
                            if (actual != cmd.expects) {
                                mutant_killing_tests.put(mutantName, cmd.label);
                            }
                        } catch (Err err) {
                            throw new RuntimeException(err.getMessage(), err.getCause());
                        }
                    }
                    mutant_order.add(mutantName);
                }

            }

            long end_mutation = System.nanoTime();
            cb(out, "", "Mutation Score: " + killedMutantsNum + "/" + totalMutantsNum + "\n");

            cb(out, "bold", "Creating mutant killing test(s) if needed.\n");
            long start_testgen = System.nanoTime();

            int i = 0;
            for (String mutant : mutant_order) {
                synchronized (SimpleReporter.class) {
                    latestModule = world;
                    latestKodkodSRC = ConstMap.make(map);
                }
                final String tempXML = tempdir + File.separatorChar + "mut" + i + ".cnf.xml";
                final String tempCNF = tempdir + File.separatorChar + "mut" + i + ".cnf";
                i++;

                rep.tempfile = tempCNF;
                int test_id = Integer.valueOf(mutant_killing_tests.get(mutant).substring(4));
                Expr valuation = CompUtil.parseOneExpression_fromString(worldRemovedFacts, valuations.get(test_id));
                Command getValuation = new Command(true, max_scope, max_scope, max_scope, valuation);
                A4Solution ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, worldRemovedFacts.getAllReachableSigs(), getValuation, options);
                String mutant_string = FileUtil.readText("results" + File.separatorChar + mutant + Names.DOT_FLT);
                rep.cb("addNonKilledMutant", mutant, tempXML, mutant_string, aunit_valuations.get(test_id), aunit_cmds.get(test_id));
            }
            long end_testgen = System.nanoTime();

            if (rep.warn > 1)
                rep.cb("bold", "Note: There were " + rep.warn + " compilation warnings. Please scroll up to see them.\n");
            if (rep.warn == 1)
                rep.cb("bold", "Note: There was 1 compilation warning. Please scroll up to see it.\n");

            long time_gen = end_gen - start_gen;
            long time_mutation = end_mutation - start_mutation;
            long time_testgen = end_testgen - start_testgen;

            rep.cb("addMuAlloyTestSummary", killedMutantsNum, (totalMutantsNum - killedMutantsNum), time_gen, time_mutation, time_testgen, modelName);
            rep.cb("finishMutation");

            /** Clean up and delete files that got created **/
            aunit_extension_executions = false;
            File delete_creations = new File("test_only_model.als");
            delete_creations.delete();
            delete_creations = new File("mutation_model.als");
            delete_creations.delete();

            dir = new File("mutants");
            File[] allContents = dir.listFiles();
            if (allContents != null) {
                for (File file : allContents) {
                    file.delete();
                }
            }
            delete_creations = new File("mutants");
            delete_creations.delete();

            dir = new File("results");
            allContents = dir.listFiles();
            if (allContents != null) {
                for (File file : allContents) {
                    file.delete();
                }
            }
            delete_creations = new File("results");
            delete_creations.delete();

            dir = new File("meta");
            allContents = dir.listFiles();
            if (allContents != null) {
                for (File file : allContents) {
                    file.delete();
                }
            }
            delete_creations = new File("meta");
            delete_creations.delete();
        }
    }
}
