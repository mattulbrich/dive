import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.io.File;
import java.util.HashMap;
import java.util.Map;

import com.sun.javadoc.ClassDoc;
import com.sun.javadoc.FieldDoc;
import com.sun.javadoc.MethodDoc;
import com.sun.javadoc.ProgramElementDoc;
import com.sun.javadoc.RootDoc;
import com.sun.javadoc.Tag;

public class DiveDoclet {
    
    private static HashMap<String, HashMap<String, String>> table =
            new HashMap<String, HashMap<String,String>>();
    private static PrintStream outStream = System.out;
    
    public static boolean start(RootDoc root) throws FileNotFoundException {
        readOptions(root.options());
        ClassDoc[] classes = root.classes();
        for (int i = 0; i < classes.length; ++i) {
            handleDiveTags(classes[i]);
            for (FieldDoc fieldDoc : classes[i].fields()) {
                handleDiveTags(fieldDoc);
            } 
            for (MethodDoc fieldDoc : classes[i].methods()) {
                handleDiveTags(fieldDoc);
            }
        }
        
        outputXML();
        
        return true;
    }
    
    private static void handleDiveTags(ProgramElementDoc doc) {
        Tag[] tags = doc.tags("divedoc");
        for (Tag tag : tags) {
            handleTag(tag);
        }
    }

    public static int optionLength(String option) {
        switch(option) {
        case "-d":
        case "-doctitle":
        case "-windowtitle":
            return 2;
        }
        return 0;
    }


    private static String readOptions(String[][] options) throws FileNotFoundException {
        String tagName = null;
        for (int i = 0; i < options.length; i++) {
            String[] opt = options[i];
            if (opt[0].equals("-d")) {
                File file = new File(opt[1], "referenceManual.xml");
                outStream = new PrintStream(new FileOutputStream(file));
            }
        }
        return tagName;
    }


    private static void outputXML() {
        outStream.println("<divedoc>");
        for (Map.Entry<String, HashMap<String, String>> entry : table.entrySet()) {
            outStream.println("  <category name=\"" + entry.getKey() + "\">");
            for (Map.Entry<String, String> entry2 : entry.getValue().entrySet()) {
                outStream.println("    <entry name=\"" + entry2.getKey() + "\">");
                outStream.println("      <![CDATA[" + entry2.getValue() + "]]>");
                outStream.println("    </entry>");
            }
            outStream.println("  </category>");
        }
        outStream.println("</divedoc>");
    }

    private static void handleTag(Tag tag) {
        String text = tag.text();
        int stringStart = text.indexOf('"', 0);
        int stringEnd = text.indexOf('"', stringStart + 1);
        
        if(stringStart == -1 || stringEnd == -1) {
            System.err.println("Ignore @divedoc: Missing descriptor at " + tag.position());
        }
        
        String[] parts = text.substring(stringStart+1, stringEnd).split("/");
        String type = parts[0]; 
        String name = parts.length > 1 ? parts[1] : "";
        
        HashMap<String, String> typeTable = table.get(type);
        if(typeTable == null) {
            typeTable = new HashMap<String, String>();
            table.put(type, typeTable);
        }
        
        typeTable.put(name, text.substring(stringEnd+1));
    }
}
