package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.references.CodeReferenceTarget;
import javafx.scene.control.*;
import org.antlr.runtime.Token;

import java.util.*;

public class CallVisualizationDialog extends Alert implements HighlightingHandler{


    private DialogPane pane;

    private Lookup lookup;

    //needs to build model and pass reference for selection model

    public CallVisualizationDialog(CallVisualizationModel model, Lookup lookup){
        super(AlertType.INFORMATION);
        this.lookup = lookup;
        pane = new SimpleListVisualizationPane(model, this);
        this.setDialogPane(pane);
        this.getButtonTypes().add(ButtonType.CLOSE);
    }


    @Override
    public void onRequestHighlight(String filename, Token startToken, Token stopToken) {
        Collection<EditorController> editorControllers = lookup.lookupAll(EditorController.class);
        ReferenceHighlightingObject referenceHighlightingObject = new ReferenceHighlightingObject();
        Set<CodeReferenceTarget> codeRefTarget = new HashSet<>();
        CodeReferenceTarget target = new CodeReferenceTarget(filename, startToken, stopToken);
        codeRefTarget.add(target);
        referenceHighlightingObject.setCodeReferenceTargetSet(codeRefTarget);
        assert editorControllers.size() == 1;
        EditorController ctrl = editorControllers.iterator().next();
        ctrl.removeReferenceHighlighting();
        ctrl.handleReferenceHighlighting(referenceHighlightingObject);
    }
}
