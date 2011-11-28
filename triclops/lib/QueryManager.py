QUERY_LIST_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>SPARQL Queries to Manage</title>
    <script
        src="codemirror/js/codemirror.js"
        type="text/javascript">
    </script>
    <style type="text/css">
      .CodeMirror {border-top: 1px solid black; border-bottom: 1px solid black;}
      .activeline {background: #f0fcff !important;}
    </style>
    <link rel="stylesheet" type="text/css" href="codemirror/css/docs.css"/>
  </head>
  <body>
    <h2>SPARQL Queries to Manage</h1>
    <table width='100%%' style='font:8pt arial,sans-serif;'>
        <tr>
          <th width=50%%' align='left'>Query name</th>
          <th align='left'>Query last modification date</th>
          <th align='left'>Date last run</th>
          <th align='left'>Number of results</th>
        </tr>
        %s
    </table>
    <hr />
    <h2>Add new query</h1>
    <form id="newQueryform" action="QUERYMGR" method="post">
        <input type="hidden" name="action" value="add"/>
        <div>
            Name: 
            <input type='text' name='name' size='100'/>
        </div>
        <div>

        <div style="border-top: 1px solid black; border-bottom: 1px solid black;">
        <textarea id="sparql" name="sparql" cols="120" rows="30">
#Example query (all classes in dataset)
SELECT DISTINCT ?Concept where {
    [] a ?Concept
}
        </textarea>
        </div>
        <script type="text/javascript">
          var editor = CodeMirror.fromTextArea('sparql', {
            height: "250px",
            parserfile: "parsesparql.js",
            stylesheet: "codemirror/css/sparqlcolors.css",
            path: "js/"
          });
        </script>
        <div>
            <input type="submit" value="Save query" />
        </div>
        </div>
      </form>
  </body>
</body>"""

QUERY_EDIT_HTML=\
"""
<html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>Editing NAME</title>
    <script
        src="codemirror/js/codemirror.js"
        type="text/javascript">
    </script>
    <style type="text/css">
      .CodeMirror {border-top: 1px solid black; border-bottom: 1px solid black;}
      .activeline {background: #f0fcff !important;}
    </style>
    <link rel="stylesheet" type="text/css" href="codemirror/css/docs.css"/>
  </head>
  <body>
  [<a href="ENDPOINT">Return</a>][<a href="http://codemirror.net/">CodeMirror</a> <a href="http://codemirror.net/1/manual.html#usage">documentation</a>]
    <form id="editQueryform" action="QUERYMGR" method="post">
        <input type="hidden" name="action" value="update"/>
        <input type="hidden" name="query" value="QUERYID"/>
        <div>
            Name:
            <input type='text' name='name' size='100' value='NAME'/>
        </div>
        <div>
        <div style="border-top: 1px solid black; border-bottom: 1px solid black;">
        <textarea id="sparql" name='sparql' cols="120" rows="500">QUERY</textarea>
        </div>
            <script type="text/javascript">
              var editor = CodeMirror.fromTextArea('sparql', {
                lineNumbers: true,
                autoMatchParens: true,
                height: "300px",
                parserfile: "parsesparql.js",
                stylesheet: "codemirror/css/sparqlcolors.css",
                path: "js/"
              });
            </script>
            <div>
              <select name="innerAction">
                <option value="update" selected="on">Update query</OPTION>
                <option value="clone" selected="on">Update query (clone)</OPTION>
                <option value="load" selected="on">Show prior results</OPTION>
                <option value="execute">Execute query (saving results)</OPTION>
              </select>
              <select name="resultFormat">
                <option value="xml" selected="on">SPARQL XML (rendered as XHTML)</OPTION>
                <option value="csv">SPARQL XML (rendered as tab delimited)</OPTION>
                <option value="csv-pure">Tab delimited</OPTION>
              </select>
            </div>
            <div>See: <a href="http://dev.mysql.com/doc/refman/5.1/en/regexp.html">Documentation</a> of MySQL REGEX expressions</div>
        </div>
        <div>
            %s
            <input type="submit" value="Go" />
        </div>
      </form>
  </body>
</body>"""
