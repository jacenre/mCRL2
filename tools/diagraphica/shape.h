//  Copyright 2007 A.j. (Hannes) pretorius. Distributed under the Boost
//  Software License, Version 1.0. (See accompanying file
//  LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
//
/// \file ./shape.h

// --- shape.h ------------------------------------------------------
// (c) 2007  -  A.J. Pretorius  -  Eindhoven University of Technology
// ---------------------------  *  ----------------------------------

#ifndef SHAPE_H
#define SHAPE_H

#include <cstddef>
#include <string>
#include <map>
using namespace std;
#include "colleague.h"
#include "dof.h"
#include "glcanvas.h"
#include "visutils.h"
#include "visualizer.h"

class Shape : public Colleague
{
public:
    // -- constructors and destructor -------------------------------
    Shape(
        Mediator* m,      const int &idx,
        const double &xC, const double &yC,
        const double &xD, const double &yD,
        const double &aC, const int    &typ);
    Shape(
        Mediator* m,      const int &idx,
        const double &xC, const double &yC,
        const double &xD, const double &yD,
        const double &xBegin, const double &yBegin,
        const double &xEnd, const double &yEnd,
	const double &aC, const int    &typ);
    Shape( const Shape &shape );
    virtual ~Shape();

    // -- set functions ---------------------------------------------
    void setIndex( const int &idx );
    void setVariable( const string &msg );
    void setVariableName( const string &msg );
    void setCheckedId( const int &id );
    void setNote( const string &msg );
    void setTextSize( const int &size );

    void setCenter( const double &xC, const double &yC );
    void setDFC( const double &xD, const double &yD );
    void setAngleCtr( const double &a );
    
    void setHinge( const double &xH, const double &yH );
    void addDOFColYValue( const double &y );
    void setDOFColYValue( const int &idx, const double &y );
    void clearDOFColYValue( const int &idx );
    void clearDOFColYValues();
    void addDOFOpaYValue( const double &y );
    void setDOFOpaYValue( const int &idx, const double &y );
    void clearDOFOpaYValue( const int &idx );
    void clearDOFOpaYValues();
    
    void setType( const int &typ );
    void setTypeNote();
    void setTypeLine();
    void setTypeRect();
    void setTypeEllipse();
    void setTypeArrow();
    void setTypeDArrow();

    void setMode( const int &typ );
    void setModeNormal();
    void setModeEdit();

    void setModeEdtDOFXCtr();
    void setModeEdtDOFYCtr();
    void setModeEdtDOFHgt();
    void setModeEdtDOFWth();
    void setModeEdtDOFAgl();
    void setModeEdtDOFCol();
    void setModeEdtDOFOpa();
    void setModeEdtDOFText();
    
    void setLineWidth( const double &w );
    void setLineColor( const ColorRGB &c );
    void setLineColor( 
        const double &r, 
        const double &g, 
        const double &b,
        const double &a );
    void setLineTransp( const double &a );
    void setFillColor( const ColorRGB &c );
    void setFillColor( 
        const double &r, 
        const double &g, 
        const double &b,
        const double &a );
    void setFillTransp( const double &a );
    void setHandleSize( const double &s );

    // -- get functions ---------------------------------------------
    int getIndex();
    int getCheckedId();
    string getNote();
    string getVariable();
    string getVariableName();
    int getTextSize();
    
    void getCenter( double &x, double &y );
    double getXCtr();
    double getYCtr();
    void getDFC( double &x, double &y );
    double getXDFC();
    double getYDFC();
    double getAngleCtr();
    void getHinge( double &x, double &y );
    double getXHinge();
    double getYHinge();

    int getType();
    int getMode();
    double getLineWidth();
    void getLineColor( ColorRGB &c );
    void getLineColor( double &r, double &g, double &b, double &a );
    double getLineTransp();
    void getFillColor( ColorRGB &c );
    void getFillColor( double &r, double &g, double &b, double &a );
    double getFillTransp();
    double getHandleSize();

    DOF* getDOFXCtr();
    DOF* getDOFYCtr();
    DOF* getDOFWth();
    DOF* getDOFHgt();
    DOF* getDOFAgl();
    DOF* getDOFCol();
    DOF* getDOFText();
    void getDOFColYValues( vector< double > &yVals );
    DOF* getDOFOpa();
    void getDOFOpaYValues( vector< double > &yVals );

    void getDOFAttrs( vector< Attribute* > &attrs );

    // -- visualization ---------------------------------------------
    void visualize( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void visualize(
        GLCanvas* canvas,
        const vector< Attribute* > attrs,
        const vector< double > attrValIdcs );
    void visualize(
        GLCanvas* canvas,
        const double &opacity,
        const vector< Attribute* > attrs,
        const vector< double > attrValIdcs );
    
    void setTransf();
    void clrTransf();

    // -- event handlers --------------------------------------------
    void handleHit( const int &hdlIdx );

    // -- public constants ------------------------------------------
    enum
    {
        TYPE_LINE,
        TYPE_RECT,
        TYPE_ELLIPSE,
        TYPE_ARROW,
        TYPE_DARROW,
        TYPE_NOTE,
        
        MODE_NORMAL,
        MODE_EDIT,
        MODE_EDT_DOF_XCTR,
        MODE_EDT_DOF_YCTR,
        MODE_EDT_DOF_HGT,
        MODE_EDT_DOF_WTH,
        MODE_EDT_DOF_AGL,
        MODE_EDT_DOF_COL,
        MODE_EDT_DOF_OPA,
        MODE_EDT_DOF_TEXT,

        ID_HDL_CTR,
        ID_HDL_TOP_LFT,
        ID_HDL_LFT,
        ID_HDL_BOT_LFT,
        ID_HDL_BOT,
        ID_HDL_BOT_RGT,
        ID_HDL_RGT,
        ID_HDL_TOP_RGT,
        ID_HDL_TOP,
        ID_HDL_ROT_RGT,
        ID_HDL_ROT_TOP,

        ID_HDL_DOF_BEG,
        ID_HDL_DOF_END,
        ID_HDL_HGE,
        ID_HDL_DIR,
    };
    static double hdlSzeHnt;
    static double minSzeHnt;
    static int    segNumHnt;    
    static ColorRGB colTxt;

protected:
    // -- private utility functions ---------------------------------
    void initDOF();
    void clearDOF();

    void handleHitEdtDOFAgl( const int &hdlIdx );
    
    // -- private visualization functions ---------------------------
    void drawNormal( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawEdit( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawText( GLCanvas* canvas );
    void drawEditDOF( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawEditDOFXCtr( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawDOFXCtr( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawEditDOFYCtr( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawDOFYCtr( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawEditDOFWth( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawDOFWth( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawEditDOFHgt( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawDOFHgt( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawEditDOFAgl( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    void drawDOFAgl( 
        const bool &inSelectMode,
        GLCanvas* canvas );
    
    // -- data members ----------------------------------------------
    
    int index;
    
    // geometry
    double xCtr,   yCtr;   // center,             [-1,1]
    double xDFC,   yDFC;   // bound dist from ctr,norm
    double aglCtr;         // rotation & incline, degrees
    
    // properties
    int      type;      // type of shape
    int      mode;      // drawing mode
    int	     szeTxt;	// font size
    double   linWth;    // line width,      pix
    ColorRGB colLin;    // line color
    ColorRGB colFil;    // fill color
    double   hdlSze;    // handle size,     pix
    int checkedVariableId; // Event id of the variable displayed on the shape;
    string	 variable;  //variable shown on the shape
    string	 variableName; // name of the variable
    string	 note;	// note shown on the shape
    GLuint  texCharId[CHARSETSIZE]; // resources for drawing text
    GLubyte texChar[CHARSETSIZE][CHARHEIGHT*CHARWIDTH]; // resources for drawing text
    bool texturesGenerated; // check whether textures for drawing text is generated or not
    GLCanvas* lastCanvas; // Last Canvas the text drawn on

    // degrees of freedom
    DOF* xCtrDOF; // composition
    DOF* yCtrDOF; // composition
    DOF* wthDOF;  // composition
    DOF* hgtDOF;  // composition
    DOF* aglDOF;  // composition
    DOF* textDOF;	  // composition
    double xHge,   yHge;   // hinge point, relative to center

    DOF* colDOF;  // composition
    vector< double > colYValues;
    DOF* opaDOF;  // composition
    vector< double > opaYValues;
};

#endif

// -- end -----------------------------------------------------------
