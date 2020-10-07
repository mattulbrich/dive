/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.browser.entities;

import de.jensd.fx.glyphs.GlyphIcons;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.util.ObservableValue;
import edu.kit.iti.algover.util.TypedBindings;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.paint.Color;
import javafx.scene.paint.Paint;

import java.util.Collections;

/**
 * Created by philipp on 12.07.17.
 */
public class PVCEntity extends TreeTableEntity {

    public enum ProofStatus {
        UNPROVEN(
                FontAwesomeIcon.EXCLAMATION,
                Color.RED,
                "No proof for this PVC"
        ),
        PROVEN(
                FontAwesomeIcon.CHECK,
                Color.LIMEGREEN,
                "Has been proven"
        ),
        SCRIPT_FAILING(
                FontAwesomeIcon.WARNING,
                Color.ORANGE,
                "Proof Script execution fails"
        ),
        DIRTY(
                FontAwesomeIcon.ASTERISK,
                Color.DARKGREY,
                "Proof Script needs to be rerun"
        ),
        MISSING_SCRIPT(
                FontAwesomeIcon.FILE_CODE_ALT,
                Color.BLUE,
                "Missing a Proof Script"
        );

        ProofStatus(GlyphIcons icon, Paint fill, String tooltip) {
            this.icon = icon;
            this.fill = fill;
            this.tooltip = tooltip;
        }

        private final GlyphIcons icon;
        private final Paint fill;
        private final String tooltip;

        public GlyphIcons getIcon() {
            return icon;
        }

        public Paint getFill() {
            return fill;
        }

        public String getTooltip() {
            return tooltip;
        }

        public static ProofStatus from(edu.kit.iti.algover.proof.ProofStatus proofStatus) {
            switch (proofStatus) {
                case CLOSED:
                    return PROVEN;
                case OPEN:
                    return UNPROVEN;
                case FAILING:
                    return SCRIPT_FAILING;
                case CHANGED_SCRIPT:
                    return DIRTY; // TODO Maybe improve these mappings
                case NON_EXISTING:
                    return MISSING_SCRIPT;
                default:
                    throw new RuntimeException("Missing case: " + proofStatus);
            }
        }
    }

    private final PVC pvc;
    private final ObjectProperty<ProofStatus> proofStatus;

    public PVCEntity(Proof proof, PVC pvc, DafnyFile location) {
        super(pvc.getIdentifier(), location, Collections.emptyList());
        this.pvc = pvc;
        // TODO: In the future somehow update this Property as soon as updates are found
        proof.addProofStatusListener(this::changed);
        this.proofStatus = new SimpleObjectProperty<>(ProofStatus.from(proof.getProofStatus()));

        if (proofStatus.get() == ProofStatus.PROVEN) {
            provenChildrenProperty().set(1);
        }
        numberChildrenProperty().set(1);
    }

    @Override
    public <T> T accept(TreeTableEntityVisitor<T> visitor) {
        return visitor.visitPVC(this);
    }

    public PVC getPVC() {
        return pvc;
    }

    public ProofStatus getProofStatus() {
        return proofStatus.get();
    }

    public ObjectProperty<ProofStatus> proofStatusProperty() {
        return proofStatus;
    }

    public void setProven() {
        proofStatus.set(ProofStatus.PROVEN);
        numberChildrenProperty().set(1);
    }

    private void changed(ObservableValue<edu.kit.iti.algover.proof.ProofStatus> observableValue, edu.kit.iti.algover.proof.ProofStatus oldValue, edu.kit.iti.algover.proof.ProofStatus newValue) {
        proofStatus.set(ProofStatus.from(newValue));
        if (proofStatus.get() == ProofStatus.PROVEN) {
            provenChildrenProperty().set(1);
        } else {
            provenChildrenProperty().set(0);
        }
    }

}
