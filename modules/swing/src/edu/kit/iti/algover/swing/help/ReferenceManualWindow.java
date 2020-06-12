/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */
package edu.kit.iti.algover.swing.help;

import java.awt.Desktop;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collections;
import java.util.List;

import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.event.HyperlinkEvent;
import javax.swing.event.HyperlinkEvent.EventType;
import javax.swing.event.HyperlinkListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import edu.kit.iti.algover.swing.util.Log;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

@SuppressWarnings("serial")
public class ReferenceManualWindow extends JFrame {

    private static final String IVIL_PROTOCOL_PREFIX = "dive:/";
    public static final String MANUAL_XML = "edu/kit/iti/algover/referenceManual.xml";

    private RMTreeNode rootNode;
    private JEditorPane contentPane;
    private JTree categoryTree;

    public ReferenceManualWindow() throws ParserConfigurationException, SAXException, IOException {
        super("DIVE - Reference Manual");
        xmlInit();
        guiInit();
    }

    private void guiInit() {
        JSplitPane splitPane = new JSplitPane();
        getContentPane().add(splitPane);
        {
            categoryTree = new JTree(rootNode);
            categoryTree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
            categoryTree.setRootVisible(false);
            categoryTree.addTreeSelectionListener(new TreeSelectionListener() {
                @Override
                public void valueChanged(TreeSelectionEvent e) {
                    setSelection(e.getPath());
                }
            });
            categoryTree.setBorder(new EmptyBorder(5, 10, 5, 0));
            JScrollPane scrollPane = new JScrollPane(categoryTree);
            splitPane.setLeftComponent(scrollPane);
        }
        {
            contentPane = new JEditorPane();
            contentPane.setEditable(false);
            contentPane.setContentType("text/html");
            contentPane.addHyperlinkListener(hyperlinkListener);
            contentPane.setBorder(BorderFactory.createEmptyBorder(10 , 10, 10, 10));
            JScrollPane scrollPane = new JScrollPane(contentPane);
            splitPane.setRightComponent(scrollPane);
        }
        setSize(1000, 400);
        splitPane.setDividerLocation(250);
    }

    private final HyperlinkListener hyperlinkListener = new HyperlinkListener() {
        @Override
        public void hyperlinkUpdate(HyperlinkEvent e) {
            if(e.getEventType() == EventType.ACTIVATED) {
                String desc = e.getDescription();
                if(desc.startsWith(IVIL_PROTOCOL_PREFIX)) {
                    TreePath path = rootNode.selectPath(desc.substring(IVIL_PROTOCOL_PREFIX.length()));
                    categoryTree.setSelectionPath(path);
                } else {
                    // TODO ensure that this works ... (isdesktop)
                    try {
                        Desktop.getDesktop().browse(e.getURL().toURI());
                    } catch (Exception ex) {
                        Log.stacktrace(ex);
                    }
                }
            }
        }
    };

    protected void setSelection(TreePath path) {
        Object lastComp = path.getLastPathComponent();
        if (lastComp instanceof RMTreeNode) {
            RMTreeNode entryElem = (RMTreeNode) lastComp;
            contentPane.setText(entryElem.getContent());
            contentPane.setCaretPosition(0);
        } else {
            contentPane.setText("");
        }
    }

    private void xmlInit() throws ParserConfigurationException, SAXException, IOException {
        InputStream is = getClass().getClassLoader().getResourceAsStream(MANUAL_XML);
        if(is == null) {
            throw new FileNotFoundException("referenceManual.xml not at its place");
        }

        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.parse(is);

        rootNode = new RMTreeNode("","");

        NodeList nodeLst = doc.getElementsByTagName("category");
        for (int s = 0; s < nodeLst.getLength(); s++) {
            Element catElement = (Element) nodeLst.item(s);
            String catName = catElement.getAttribute("name");
            RMTreeNode catNode = new RMTreeNode(catName, "");
            rootNode.add(catNode);
            NodeList entryList = catElement.getElementsByTagName("entry");
            for (int r = 0; r < entryList.getLength(); r++) {
                Element entryElement = (Element) entryList.item(r);
                String entryName = entryElement.getAttribute("name");
                String content = entryElement.getTextContent();
                if(entryName.length() == 0) {
                    catNode.setContent(content);
                } else {
                    catNode.add(new RMTreeNode(entryName, content));
                }
            }
        }

        for (RMTreeNode node : rootNode.getChildren()) {
            Collections.sort(node.getChildren());
        }

    }

    private static class RMTreeNode
            extends DefaultMutableTreeNode
            implements Comparable<RMTreeNode> {

        private String content;

        public RMTreeNode(String name, String content) {
            super(name);
            this.content = content;
        }

        public void setContent(String content) {
            this.content = content;
        }

        public String getContent() {
            return content;
        }

        public String getName() {
            return (String)getUserObject();
        }

        @SuppressWarnings("unchecked")
        public List<RMTreeNode> getChildren() {
            if(children == null) {
                return Collections.emptyList();
            } else {
                return (List)children;
            }
        }

        @Override
        public int compareTo(RMTreeNode o) {
            return getName().compareToIgnoreCase(o.getName());
        }

        public TreePath selectPath(String path) {
            String[] comps = path.split("/");
            return selectPath0(comps, new TreePath(this));
        }

        private TreePath selectPath0(String[] comps, TreePath path) {
            int no = path.getPathCount() - 1;
            if(no == comps.length) {
                return path;
            }

            for (RMTreeNode child : getChildren()) {
                if(comps[no].equals(child.getName())) {
                    return child.selectPath0(comps, path.pathByAddingChild(child));
                }
            }
            return null;
        }
    }

    public static void main(String[] args) throws ParserConfigurationException, SAXException, IOException {
        JFrame f = new ReferenceManualWindow();
        f.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
        f.setVisible(true);
    }

}
