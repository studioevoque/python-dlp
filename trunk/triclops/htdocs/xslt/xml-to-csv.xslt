<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    xmlns:sr="http://www.w3.org/2005/sparql-results#"
    xmlns="http://www.w3.org/1999/xhtml"
    version="1.0">
  <xsl:output method="text" version="1.0" encoding="UTF-8" indent="yes" />
  <xsl:template match="node()|@*|text()"/>
  <xsl:template match="text()" mode="header"/>
  <xsl:template match="node()" mode="results"/>
  <xsl:template match="/">
    <xsl:apply-templates select="sr:sparql"/>
  </xsl:template>
  <xsl:template match="sr:sparql">
    <xsl:apply-templates select="sr:head/sr:variable" mode="header"/>
    <xsl:apply-templates select="sr:results/sr:result" mode="results"/>
  </xsl:template>
  <xsl:template match="sr:result" mode="results">
    <xsl:variable name="resultPos" select="position()"/>
    <xsl:for-each select="/sr:sparql/sr:head/sr:variable/@name">
      <xsl:variable name="varName" select="."/>
      <xsl:variable name="notLast" select="position()!=last()"/>
      <xsl:if test="/sr:sparql/sr:results/sr:result[$resultPos]/sr:binding[@name = $varName]">
        <!-- This result has a binding for the current variable -->
        <xsl:value-of select="/sr:sparql/sr:results/sr:result[$resultPos]/sr:binding[@name = $varName]/*" />
      </xsl:if>
      <!--  write out the delimeter -->
      <xsl:call-template name="delimiters">
        <xsl:with-param name="notLast" select="$notLast"/>
      </xsl:call-template>
    </xsl:for-each>
  </xsl:template>
  <xsl:template name="delimiters">
    <xsl:param name="notLast"/>
    <xsl:choose>
      <xsl:when test="$notLast">
        <xsl:text>&#x9;</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>&#10;</xsl:text>
      </xsl:otherwise>
    </xsl:choose>    
  </xsl:template>
  <xsl:template match="sr:variable" mode="header">
    <xsl:value-of select="@name"/>
    <xsl:call-template name="delimiters">
      <xsl:with-param name="notLast" select="position()!=last()"/>
    </xsl:call-template>
  </xsl:template>
  <xsl:template match="sr:literal|sr:uri|sr:bnode" mode="results">
    <xsl:value-of select="text()"/>
  </xsl:template>
</xsl:stylesheet>