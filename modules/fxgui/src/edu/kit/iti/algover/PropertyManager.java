package edu.kit.iti.algover;

import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.proof.ProofNodeSelector;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.TypedBindings;
import javafx.beans.binding.Bindings;
import javafx.beans.property.SimpleObjectProperty;

/**
 * This class holds all relevant properties for the FXGUI.
 * It is implemented as a Singleton so to access properties the getInstance() method is used.
 */
public class PropertyManager {
    /**
     * the {@link ProofNodeSelector} pointing to the {@link ProofNode} that is currently displayed in the sequent view
     * this selector is bound bidirectionally with {@link PropertyManager#currentProofNode} so updates to either one of
     * them will be mirrored by the other one
     */
    public SimpleObjectProperty<ProofNodeSelector> currentProofNodeSelector = new SimpleObjectProperty<>();

    /**
     * The {@link ProofNode} that is currently displayed in the sequent view
     * it is bound bidirectionally with {@link PropertyManager#currentProofNodeSelector} so updates to either one of
     * them will be mirrored by the other one
     */
    public SimpleObjectProperty<ProofNode> currentProofNode = new SimpleObjectProperty<>();

    /**
     * The proof that is currently displayed (corresponding to the selected PVC and seen in the Scriptview as script)
     */
    public SimpleObjectProperty<Proof> currentProof = new SimpleObjectProperty<>();

    /**
     * The singleton instance
     */
    private static PropertyManager instance;

    /**
     * Provides the singleton for this class
     * @return an instance of this class
     */
    public static PropertyManager getInstance() {
        if (instance == null) {
            instance = new PropertyManager();
        }
        return instance;
    }

    private PropertyManager() {
        TypedBindings.bind(currentProofNode, currentProofNodeSelector,
                (proofNode -> new ProofNodeSelector(proofNode)),
                proofNodeSelector -> {
                    try {
                        return proofNodeSelector.get(currentProof.get());
                    } catch (RuleException e) {
                        e.printStackTrace();
                    }
                    return null;
                });
    }
}

