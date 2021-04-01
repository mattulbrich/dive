/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * DIVE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public LicenS* along with DIVE.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.Proof;
import javafx.concurrent.Worker;
import javafx.event.EventHandler;
import javafx.scene.control.ButtonType;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.Dialog;
import javafx.scene.layout.VBox;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;
import javafx.stage.PopupWindow;
import javafx.stage.Window;
import netscape.javascript.JSException;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.events.EventListener;
import org.w3c.dom.events.EventTarget;

import java.util.Iterator;
import java.util.NoSuchElementException;

public class BlocklyView extends VBox {
    private final WebView webView;
    private final WebEngine engine;

    private final ScriptViewListener listener;

    private ScriptHTML scriptHTML;

    public BlocklyView(ScriptViewListener listener) {
        this.listener = listener;

        webView = new WebView();

        webView.setContextMenuEnabled(false);

        // optional set custom context menu
        /*webView.setOnContextMenuRequested(new EventHandler<ContextMenuEvent>() {
            @Override
            public void handle(ContextMenuEvent event) {
                final Iterator<Window> windows = Window.getWindows().iterator();
                while (windows.hasNext()) {
                    Window win = null;
                    try {
                        win = windows.next();
                    } catch (NoSuchElementException ex) {
                        // somehow iteration fail (hasNext() might return
                        // true even if elem does not exist anymore.
                        return;
                    }
                    if (win instanceof ContextMenu) {
                        // create custom context menu here
                        win.hide();
                    }
                }
            }
        });*/

        engine = webView.getEngine();
        engine.setJavaScriptEnabled(true);
        engine.setOnAlert(event -> showAlert(event.getData()));

        // Add event listeners to html elements after the site is loaded.
        engine.getLoadWorker().stateProperty().addListener(
                (observable, oldValue, newValue) -> {
                    if (newValue != Worker.State.SUCCEEDED) {
                        return;
                    }
                    Document doc = engine.getDocument();

                    if (scriptHTML.getProofScript() != null) {
                        scriptHTML.getProofScript().accept(
                                new DefaultScriptASTVisitor<Void, Void, RuntimeException>() {

                                    @Override
                                    protected Void visitDefault(ScriptAST ast, Void arg) throws RuntimeException {
                                        Integer elemID = scriptHTML.getID(ast);
                                        addHTMLElemListeners(doc, elemID, evt -> {
                                            evt.stopPropagation();
                                            listener.onASTElemSelected(ast);
                                        });
                                        return null;
                                    }

                                    @Override
                                    protected void visitStatements(ScriptAST.StatementList statementList, Void arg) throws RuntimeException {
                                        visitDefault(statementList, arg);
                                        for (ScriptAST.Statement statement : statementList.getStatements()) {
                                            statement.accept(this, arg);
                                        }
                                    }

                                    @Override
                                    public Void visitCommand(ScriptAST.Command command, Void arg) throws RuntimeException {
                                        visitDefault(command, arg);
                                        return null;
                                    }

                                    @Override
                                    public Void visitCases(ScriptAST.Cases cases, Void arg) throws RuntimeException {
                                        visitDefault(cases, arg);
                                        for (ScriptAST.Case aCase : cases.getCases()) {
                                            aCase.accept(this, arg);
                                        }
                                        return null;
                                    }


                                }, null
                        );
                    }

                    listener.onViewReloaded();
                }
        );

        initView();
        update();
    }

    private boolean addHTMLElemListeners(Document doc, Integer id, EventListener listener) {
        if (id == null) {
            // TODO: logging
            return false;
        }
        Element el = doc.getElementById(String.valueOf(id));
        // TODO: remove listener ?
        if (el != null) {
            // useCapture parameter of addEventListener method influences the direction of event propagation.
            // See HTML/JavaScript specification for exact description.
            // For HTML documents: true ~ top down, false ~ bottom up
            ((EventTarget) el).addEventListener("click", listener, false);
            return true;
        } else {
            // TODO: log somewhere (not for user)
            System.out.println("Statement with id " + id + " not found in HTMl Document.");
        }
        return false;
    }


    private void initView() {
        this.getChildren().setAll(this.webView);
    }

    private void showAlert(String message) {
        Dialog<Void> alert = new Dialog<>();
        alert.getDialogPane().setContentText(message);
        alert.getDialogPane().getButtonTypes().add(ButtonType.OK);
        alert.showAndWait();
    }


    /**
     * Create html representation of current proof and reload page.
     */
    public void update() {
        Proof currentProof = PropertyManager.getInstance().currentProof.get();
        executeJavaScript("resetError();");
        if (currentProof != null) {
            scriptHTML = new ScriptHTML(PropertyManager.getInstance().currentProof.get().getProofScript());
        } else {
            scriptHTML = new ScriptHTML(null);
        }

        engine.loadContent(scriptHTML.getHTML());
    }


    public void highlight(ScriptAST astElem) {
        Integer elemid = scriptHTML.getID(astElem);
        if (elemid != null) {
            executeJavaScript("highlight(" + elemid + ");");
        }
    }

    public void unhighlight(ScriptAST astElem) {
        Integer elemid = scriptHTML.getID(astElem);
        if (elemid != null) {
            executeJavaScript("unhighlight(" + elemid + ");");
        }
    }

    public void setOpenProofEnd (ScriptAST.StatementList statementList) {
        Integer elemid = scriptHTML.getID(statementList);
        if (elemid != null) {
            executeJavaScript("setOpenEnd(" + elemid + ");");
        }
    }

    public void setClosedProofEnd (ScriptAST statementList) {
        Integer elemid = scriptHTML.getID(statementList);
        if (elemid != null) {
            statementList.accept(new DefaultScriptASTVisitor<Void, Void, RuntimeException>() {
                @Override
                public Void visitScript(ScriptAST.Script script, Void arg) throws RuntimeException {
                    executeJavaScript("setStyle(" + elemid + ", " + "\"closedScript\"" + ");");
                    return null;
                }

                @Override
                public Void visitCase(ScriptAST.Case aCase, Void arg) throws RuntimeException {
                    executeJavaScript("setStyle(" + elemid + ", " + "\"closedCase\"" + ");");
                    return null;
                }
            }, null);
        }
    }

    public void highlightError(ScriptAST scriptAST) {
        Integer elemid = scriptHTML.getID(scriptAST);
        executeJavaScript("setError(" + elemid + ");");
    }

    public void highlightUnreachedCode(ScriptAST scriptAST) {
        Integer elemid = scriptHTML.getID(scriptAST);
        executeJavaScript("setStyle(" + elemid + ", " + "\"ignore\"" + ");");
    }
    
    public void hideProofEnd (ScriptAST statementList) {
        Integer elemid = scriptHTML.getID(statementList);
        if (elemid != null) {
            executeJavaScript("hide(" + elemid + ");");
        }
    }

    private void executeJavaScript(String js) {
        try {
            engine.executeScript(js);
        } catch (JSException jsex) {
            System.out.println("Failed to run javascript code, due to js exception: " + jsex.getMessage());
        }
    }

}
