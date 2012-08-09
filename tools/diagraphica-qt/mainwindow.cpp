// Author(s): A.J. (Hannes) Pretorius, Ruud Koolen
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)

#include "mainwindow.h"
#include "combnplot.h"
#include "corrlplot.h"
#include "distrplot.h"
#include "mcrl2/lts/lts_io.h"
#include <QTableWidgetItem>
#include <QMessageBox>


MainWindow::MainWindow():
  m_settingsDialog(new SettingsDialog(this, &m_settings)),
  m_graph(0),
  m_examiner(0),
  m_arcDiagram(0),
  m_simulator(0),
  m_timeSeries(0),
  m_diagramEditor(0)
  {
  m_ui.setupUi(this);

  m_ui.attributes->resizeColumnsToContents();
  m_ui.domain->resizeColumnsToContents();

  connect(m_ui.actionOpen, SIGNAL(triggered()), this, SLOT(openFile()));
  connect(m_ui.actionSave, SIGNAL(triggered()), this, SLOT(saveFile()));
  connect(m_ui.actionSaveAs, SIGNAL(triggered()), this, SLOT(saveFileAs()));

//  connect(m_ui.actionOpenAttributes, SIGNAL(triggered()), this, SLOT(openAttributeConfiguration()));
//  connect(m_ui.actionSaveAttributes, SIGNAL(triggered()), this, SLOT(saveAttributeConfiguration()));

//  connect(m_ui.actionOpenDiagram, SIGNAL(triggered()), this, SLOT(openDiagram()));
//  connect(m_ui.actionSaveDiagram, SIGNAL(triggered()), this, SLOT(saveDiagram()));

  connect(m_ui.actionQuit, SIGNAL(triggered()), QCoreApplication::instance(), SLOT(quit()));

  connect(m_ui.actionSettingsGeneral, SIGNAL(triggered()), m_settingsDialog, SLOT(showGeneral()));
  connect(m_ui.actionSettingsArcDiagram, SIGNAL(triggered()), m_settingsDialog, SLOT(showArcDiagram()));

  connect(m_ui.attributes, SIGNAL(customContextMenuRequested(const QPoint &)), this, SLOT(showAttributeContextMenu(const QPoint &)));
  m_ui.attributes->setContextMenuPolicy(Qt::CustomContextMenu);
  connect(m_ui.attributes, SIGNAL(itemSelectionChanged()), this, SLOT(updateAttributeOperations()));
  updateAttributeOperations();

  connect(m_ui.actionClusterNodes, SIGNAL(triggered()), this, SLOT(clusterNodes()));
  connect(m_ui.actionViewTrace, SIGNAL(triggered()), this, SLOT(viewTrace()));
  connect(m_ui.actionDistributionPlot, SIGNAL(triggered()), this, SLOT(distributionPlot()));
  connect(m_ui.actionCorrelationPlot, SIGNAL(triggered()), this, SLOT(correlationPlot()));
  connect(m_ui.actionCombinationPlot, SIGNAL(triggered()), this, SLOT(combinationPlot()));
  connect(m_ui.actionDuplicate, SIGNAL(triggered()), this, SLOT(duplicateAttribute()));
  connect(m_ui.actionRenameAttribute, SIGNAL(triggered()), this, SLOT(renameAttribute()));
  connect(m_ui.actionDelete, SIGNAL(triggered()), this, SLOT(deleteAttribute()));
}

static void stretch(QWidget *widget)
{
  widget->parentWidget()->layout()->addWidget(widget);
}

void MainWindow::open(QString filename)
{
  Graph *graph = new Graph(this);
  graph->setFileName(filename);
  try
  {
    QProgressDialog dialog(QString("Opening ") + filename, QString(), 0, 1, this);
    connect(&m_parser, SIGNAL(started(int)), &dialog, SLOT(setMaximum(int)));
    connect(&m_parser, SIGNAL(progressed(int)), &dialog, SLOT(setValue(int)));
    dialog.show();

    m_parser.parseFile(filename, graph);

    graph->initGraph();
  }
  catch (const mcrl2::runtime_error& e)
  {
    QMessageBox::critical(this, "Error", QString::fromStdString(e.what()));
    delete graph;
    return;
  }

  QList<QWidget *> oldWidgets = QList<QWidget *>()
      << m_diagramEditor
      << m_examiner
      << m_arcDiagram
      << m_simulator
      << m_timeSeries;

  for (int i = 0; i < oldWidgets.size(); i++)
  {
    delete oldWidgets[i];
  }
  oldWidgets.clear();

  if (graph != 0)
  {
    emit closingGraph();
    delete m_graph;
  }

  m_graph = graph;

  m_ui.numberOfStates->setText(QString::number(m_graph->getSizeNodes()));
  m_ui.numberOfTransitions->setText(QString::number(m_graph->getSizeEdges()));

  m_diagramEditor = new DiagramEditor(m_ui.diagramEditorWidget, this, m_graph);
  stretch(m_diagramEditor);

  m_examiner = new Examiner(m_ui.examinerWidget, this, &m_settings, m_graph);
  m_examiner->setDiagram(m_diagramEditor->getDiagram());
  stretch(m_examiner);

  m_arcDiagram = new ArcDiagram(m_ui.arcDiagramWidget, this, &m_settings, m_graph);
  m_arcDiagram->setDiagram(m_diagramEditor->getDiagram());
  stretch(m_arcDiagram);

  m_simulator = new Simulator(m_ui.simulatorWidget, this, &m_settings, m_graph);
  m_simulator->setDiagram(m_diagramEditor->getDiagram());
  stretch(m_simulator);

  m_timeSeries = new TimeSeries(m_ui.traceWidget, this, &m_settings, m_graph);
  m_timeSeries->setDiagram(m_diagramEditor->getDiagram());
  stretch(m_timeSeries);

  m_ui.attributes->setRowCount(0);
  for (size_t i = 0; i < m_graph->getSizeAttributes(); i++)
  {
    m_ui.attributes->insertRow(i);
    for (int j = 0; j < m_ui.attributes->columnCount(); j++)
    {
      m_ui.attributes->setItem(i, j, new QTableWidgetItem());
      m_ui.attributes->item(i, j)->setFlags(Qt::ItemIsSelectable | Qt::ItemIsDragEnabled | Qt::ItemIsEnabled);
    }

    Attribute *attribute = m_graph->getAttribute(i);
    m_ui.attributes->item(i, 0)->setText(QString::number(i));
    m_ui.attributes->item(i, 1)->setText(attribute->name());
    m_ui.attributes->item(i, 2)->setText(attribute->type());
    m_ui.attributes->item(i, 3)->setText(QString::number(attribute->getSizeCurValues()));
  }

  m_ui.attributes->resizeColumnsToContents();

  updateAttributeOperations();
}

void MainWindow::save(QString filename)
{
  try
  {
    QProgressDialog dialog(QString("Saving ") + filename, QString(), 0, 1, this);
    connect(&m_parser, SIGNAL(started(int)), &dialog, SLOT(setMaximum(int)));
    connect(&m_parser, SIGNAL(progressed(int)), &dialog, SLOT(setValue(int)));
    dialog.show();

    m_parser.writeFSMFile(filename, m_graph);

    m_graph->setFileName(filename);
  }
  catch (const mcrl2::runtime_error& e)
  {
    QMessageBox::critical(this, "Error", QString::fromStdString(e.what()));
    return;
  }
}

void MainWindow::openFile()
{
  QString filter = QString("All supported files (") + QString::fromStdString(mcrl2::lts::detail::lts_extensions_as_string(" ")) + ");;All files (*.*)";
  QString filename = QFileDialog::getOpenFileName(this, "Open LTS", QString(), filter);
  if (filename.isNull())
  {
    return;
  }

  open(filename);
}

void MainWindow::saveFile()
{
  if (m_graph == NULL)
  {
    return;
  }
  QString filter = QString("FSM files (*.fsm);;All files (*.*)");
  QString filename = m_graph->filename();

  if (filename.isNull() || QFileInfo(filename).suffix().toLower() != "fsm")
  {
    filename = QFileDialog::getSaveFileName(this, "Save LTS", QString(), filter);
  }
  if (filename.isNull())
  {
    return;
  }
  save(filename);
}

void MainWindow::saveFileAs()
{
  if (m_graph == NULL)
  {
    return;
  }
  QString filter = QString("FSM files (*.fsm);;All files (*.*)");
  QString filename = QFileDialog::getSaveFileName(this, "Save LTS", QString(), filter);

  if (filename.isNull())
  {
    return;
  }
  save(filename);
}

void MainWindow::showAttributeContextMenu(const QPoint &position)
{
  m_ui.menuAttributes->popup(m_ui.attributes->viewport()->mapToGlobal(position));
}

void MainWindow::updateAttributeOperations()
{
  QList<int> attributes = selectedAttributes();
  int items = attributes.size();

  m_ui.actionClusterNodes->setEnabled(items > 0);
  m_ui.actionViewTrace->setEnabled(items > 0);
  m_ui.actionDistributionPlot->setEnabled(items == 1);
  m_ui.actionCorrelationPlot->setEnabled(items == 2);
  m_ui.actionCombinationPlot->setEnabled(items > 0);
  m_ui.actionDuplicate->setEnabled(items == 1);
  m_ui.actionRenameAttribute->setEnabled(items == 1);
  m_ui.actionDelete->setEnabled(items > 0);

  m_ui.domain->setRowCount(0);
  if (attributes.size() == 1)
  {
    assert(attributes[0] < m_graph->getSizeAttributes());

    std::vector<size_t> valueDistribution;
    m_graph->calcAttrDistr(attributes[0], valueDistribution);

    Attribute *attribute = m_graph->getAttribute(attributes[0]);
    for (size_t i = 0; i < attribute->getSizeCurValues(); i++)
    {
      Value *value = attribute->getCurValue(i);

      m_ui.domain->insertRow(i);
      for (int j = 0; j < m_ui.attributes->columnCount(); j++)
      {
        m_ui.domain->setItem(i, j, new QTableWidgetItem());
        m_ui.domain->item(i, j)->setFlags(Qt::ItemIsSelectable | Qt::ItemIsDragEnabled | Qt::ItemIsEnabled);
      }

      m_ui.domain->item(i, 0)->setText(QString::number(i));
      m_ui.domain->item(i, 1)->setText(QString::fromStdString(value->getValue()));
      m_ui.domain->item(i, 2)->setText(QString::number(valueDistribution[i]));
      m_ui.domain->item(i, 3)->setText(QString::number(100 * valueDistribution[i] / (double)m_graph->getSizeNodes()));
    }
  }
}

void MainWindow::clusterNodes()
{

}

void MainWindow::viewTrace()
{

}

void MainWindow::distributionPlot()
{
  QList<int> attributes = selectedAttributes();
  if (attributes.size() != 1)
  {
    return;
  }

  DistrPlot *plot = new DistrPlot(0, m_graph, attributes[0]);
  connect(this, SIGNAL(closingGraph()), plot, SLOT(close()));
  plot->setAttribute(Qt::WA_DeleteOnClose);
  plot->setDiagram(m_diagramEditor->getDiagram());
  plot->show();
}

void MainWindow::correlationPlot()
{
  QList<int> attributes = selectedAttributes();
  if (attributes.size() != 2)
  {
    return;
  }

  CorrlPlot *plot = new CorrlPlot(0, m_graph, attributes[0], attributes[1]);
  connect(this, SIGNAL(closingGraph()), plot, SLOT(close()));
  plot->setAttribute(Qt::WA_DeleteOnClose);
  plot->setDiagram(m_diagramEditor->getDiagram());
  plot->show();
}

void MainWindow::combinationPlot()
{
  QList<int> attributes = selectedAttributes();
  if (attributes.size() == 0)
  {
    return;
  }
  std::vector<size_t> attributeVector;
  for (int i = 0; i < attributes.size(); i++)
  {
    attributeVector.push_back(attributes[i]);
  }

  CombnPlot *plot = new CombnPlot(0, m_graph, attributeVector);
  connect(this, SIGNAL(closingGraph()), plot, SLOT(close()));
  plot->setAttribute(Qt::WA_DeleteOnClose);
  plot->setDiagram(m_diagramEditor->getDiagram());
  plot->show();
}

void MainWindow::duplicateAttribute()
{

}

void MainWindow::renameAttribute()
{

}

void MainWindow::deleteAttribute()
{

}



QList<int> MainWindow::selectedAttributes()
{
  QList<int> output;
  QList<QTableWidgetSelectionRange> ranges = m_ui.attributes->selectedRanges();
  for (int i = 0; i < ranges.size(); i++)
  {
    for (int j = ranges[i].topRow(); j <= ranges[i].bottomRow(); j++)
    {
      output += j;
    }
  }
  return output;
}

