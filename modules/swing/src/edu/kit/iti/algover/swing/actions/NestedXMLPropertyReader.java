/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;
import java.util.Stack;

import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;

import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.SimpleLog;
import edu.kit.iti.algover.util.Util;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.DefaultHandler;

// TODO DOC
public class NestedXMLPropertyReader extends DefaultHandler {

    private Properties properties = new Properties();
    
    private boolean ignoreFirstElement;
    
    private Stack<String> stack = new Stack<String>();

    private StringBuilder content = new StringBuilder();

    private NestedXMLPropertyReader(boolean ignoreRoot) {
        this.ignoreFirstElement = ignoreRoot;
    }

    public static Properties read(File file, boolean ignoreRoot) throws IOException {
        return read(new FileInputStream(file), ignoreRoot);
    }
    
    public static Properties read(InputStream is, boolean ignoreRoot) throws IOException {
        SAXParserFactory factory = SAXParserFactory.newInstance();
        try {
            SAXParser parser = factory.newSAXParser();
            NestedXMLPropertyReader handler = new NestedXMLPropertyReader(ignoreRoot);
            parser.parse(is, handler);
            return handler.properties ;
        } catch (IOException e) {
            throw e;
        } catch (Exception e) {
            throw new IOException(e);
        }
    }
    
    @Override
    public void startElement(String uri, String localName,
            String name, Attributes attributes) throws SAXException {
        
        Log.enter(uri, localName, name, attributes);
        
        if(ignoreFirstElement) {
            // ignore this but no more!
            Log.log(Log.TRACE, "ignore element: " + name);
            ignoreFirstElement = false;
            return;
        }
        
        if(content.length() > 0) {
            String newcontent = content.toString().replaceAll("\\s+", " ").trim();
            if(newcontent.length() > 0) {
                String key = Util.join(stack, ".");
                if(properties.containsKey(key)) {
                    Log.log(Log.WARNING, "Duplicated key: " + key);
                }

                properties.put(key, newcontent);
            }
            content.setLength(0);
        }
        
//        if(name.indexOf('.') != -1) {
//            throw new SAXException("A name includes a '.': " + name);
//        }
        
        stack.push(name);
        
        String prefix = Util.join(stack, ".");
        
        for (int i = 0; i < attributes.getLength(); i++) {
            String key = prefix + "." + attributes.getQName(i);
            String value = attributes.getValue(i);
            if(properties.containsKey(key)) {
                Log.log(Log.WARNING, "Duplicated key: " + key);
            }
            properties.put(key, value);
        }
        
        Log.leave();
    }
    
    @Override
    public void endElement(String uri, String localName, String name)
            throws SAXException {
        Log.enter(uri, localName, name);
        
        
        if(content.length() > 0) {

            String newcontent = content.toString().replaceAll("\\s+", " ").trim();
            if(newcontent.length() > 0) {
                String key = Util.join(stack, ".");
                if(properties.containsKey(key)) {
                    Log.log(Log.WARNING, "Duplicated key: " + key);
                }

                properties.put(key, newcontent);
            }
            content.setLength(0);
        }
        
        // if the first element has been ignored, this may indeed by the case!
        if(!stack.isEmpty()) {
            stack.pop();
        }
        
        Log.leave();
    }
    
    @Override
    public void characters(char[] ch, int start, int length)
            throws SAXException {
        Log.enter(new String(ch, start, length));
        
        content.append(ch, start, length);
    }
        
    public static void main(String[] args) throws Exception {
         SimpleLog sl = new SimpleLog();
         sl.setMinLevel(20);
         Log.setLogImplementation(sl);
         Properties prop = NestedXMLPropertyReader.read(NestedXMLPropertyReader.class.getResourceAsStream("menu.xml"), true);
         prop.list(System.out);
         System.out.println(prop);
    }
}
