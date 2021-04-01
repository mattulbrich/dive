/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Foobar is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.util;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ScriptASTUtilTest {

    @Test
    public void insertNonExistingCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight;");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(2, updatedScript.getStatements().size());
        assertTrue(updatedScript.getStatements().get(1) instanceof ScriptAST.Cases);
        assertEquals(2, ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().size());
        assertEquals("\"case 1\"", ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().get(0).getLabel().getText());
        assertEquals("\"case 2\"", ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().get(1).getLabel().getText());
    }

    @Test
    public void insertEmptyCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight; cases {}");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(2, updatedScript.getStatements().size());
        assertTrue(updatedScript.getStatements().get(1) instanceof ScriptAST.Cases);
        assertEquals(2, ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().size());
        assertEquals("\"case 1\"", ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().get(0).getLabel().getText());
        assertEquals("\"case 2\"", ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().get(1).getLabel().getText());
    }

    @Test
    public void insertEmptyNestedCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight; cases { \"case 1\": branchCut with='true'; cases {}}");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(2, updatedScript.getStatements().size());
        assertTrue(updatedScript.getStatements().get(1) instanceof ScriptAST.Cases);
        assertEquals(1, ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().size());
        assertEquals("\"case 1\"", ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().get(0).getLabel().getText());
        assertEquals("andRight;\n" +
                        "cases {\n" +
                        "  \"case 1\":\n" +
                        "    branchCut with='true';\n" +
                        "    cases {\n" +
                        "      \"positive\":\n" +
                        "      \"negative\":\n" +
                        "    }\n" +
                        "}",
                updatedScript.toString());
    }

    @Test
    public void insertMissingNestedCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight; cases { \"case 1\": branchCut with='true'; }");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(2, updatedScript.getStatements().size());
        assertTrue(updatedScript.getStatements().get(1) instanceof ScriptAST.Cases);
        assertEquals(1, ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().size());
        assertEquals("\"case 1\"", ((ScriptAST.Cases) updatedScript.getStatements().get(1)).getCases().get(0).getLabel().getText());
        assertEquals("andRight;\n" +
                "cases {\n" +
                "  \"case 1\":\n" +
                "    branchCut with='true';\n" +
                "    cases {\n" +
                "      \"positive\":\n" +
                "      \"negative\":\n" +
                "    }\n" +
                "}",
                updatedScript.toString());
    }

    @Test
    public void insertPartialNestedCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight; cases { \"case 1\": branchCut with='true'; cases { \"positive\": }}");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(proof.getProofScript().toString(), updatedScript.toString());
    }

    @Test
    public void insertExistingCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight; cases { \"case 1\": \"case 2\": }");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(proof.getProofScript().toString(), updatedScript.toString());
    }

    @Test
    public void insertPartlyExistingCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptTextAndInterpret("andRight; cases { \"case 1\": }");
        ScriptAST.Script updatedScript = ScriptASTUtil.insertMissingCases(proof.getProofRoot(), proof.getProofScript());
        assertEquals(proof.getProofScript().toString(), updatedScript.toString());
    }

}
