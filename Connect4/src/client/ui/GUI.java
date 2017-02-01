package client.ui;

import java.awt.BorderLayout;
import java.awt.Font;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.IOException;
import java.util.Observable;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JTextPane;

import client.Client;

public class GUI extends View implements ActionListener {

	public static JFrame frameGUI;
	private JTextArea fieldArea;
	private JTextArea internMessages;
	private JTextArea chatMessages;
	private JTextField outwardChat;
	private JButton sendChat;
	private JButton gameStart;
	
	public GUI(Client client) {
		super(client);
		frameGUI = new JFrame("Connect4 GUI");
		frameGUI.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frameGUI.setResizable(false);
		
		JPanel div = new JPanel(new BorderLayout());
		JPanel p1 = new JPanel();
		p1.setBorder(BorderFactory.createTitledBorder("Field"));
		fieldArea = new JTextArea(10, 80);
		fieldArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
		fieldArea.setEditable(false);
		p1.add(fieldArea);
		div.add(BorderLayout.NORTH, p1);
		
		JPanel p2 = new JPanel();
		p2.setBorder(BorderFactory.createTitledBorder("Console"));
		internMessages = new JTextArea(10, 50);
		internMessages.setEditable(false);
		internMessages.setLineWrap(true);
		internMessages.setWrapStyleWord(true);
		JScrollPane scroll = new JScrollPane (internMessages, 
				JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		p2.add(scroll);
		div.add(BorderLayout.SOUTH, p2);
		
		JPanel p3 = new JPanel(new BorderLayout());
		p3.setBorder(BorderFactory.createTitledBorder("Chat"));
		chatMessages = new JTextArea(21, 30);
		chatMessages.setEditable(false);
		chatMessages.setLineWrap(true);
		chatMessages.setWrapStyleWord(true);
		outwardChat = new JTextField();
		sendChat = new JButton("Send");
		sendChat.addActionListener(this);
		p3.add(BorderLayout.NORTH, chatMessages);
		p3.add(BorderLayout.CENTER, outwardChat);
		p3.add(BorderLayout.EAST, sendChat);

		gameStart = new JButton("New game");
		gameStart.addActionListener(this);
		gameStart.setEnabled(true);
		
		frameGUI.add(BorderLayout.CENTER, div);
		frameGUI.add(BorderLayout.EAST, p3);
		frameGUI.add(BorderLayout.SOUTH, gameStart);
		
		frameGUI.pack();
		frameGUI.setVisible(true);
	}

	@Override
	public void update(Observable o, Object arg) {
		fieldArea.setText(o.toString());
		if (arg != null && arg.equals("START")) {
			gameStart.setEnabled(false);
		} else if (arg != null && arg.equals("END")) {
			gameStart.setEnabled(true);
		}
	}

	@Override
	public void userInput(String input) {
		//Do nothing
	}

	@Override
	public void internalMessage(String msg) {
		internMessages.append(msg + "\n");
	}

	@Override
	public void chatMessage(String msg) {
		chatMessages.append(msg + "\n");
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == gameStart) {
			try {
				control.client.getProtocoller().cmdGameRequest();
				internalMessage("Game request sent");
			} catch (IOException e1) {
				internalMessage("Something went wrong while sending game request");
			}
		} else if (e.getSource() == sendChat) {
			if (!outwardChat.getText().equals("")) {
				try {
					client.getProtocoller().cmdChat(outwardChat.getText());
					outwardChat.setText("");
				} catch (IOException e1) {
					System.err.println("Error while sending chat");
					internalMessage("Something went wrong while sending chat");
				}
			}
		} else if (e.getSource() == moveOK) {
			moveInputLock.lock();
			try {
				moveInput = moveInputField.getText();
				moveInputted.signal();
			} finally {
				moveInputLock.unlock();
			}
		}
	}

	private String moveInput = null;
	private JButton moveOK;
	private JTextField moveInputField;
	private JDialog moveDialog;
	private static ReentrantLock moveInputLock = new ReentrantLock();
	private static Condition moveInputted = moveInputLock.newCondition();
	synchronized public String getMove() {
		moveInputLock.lock();
		try {
			moveDialog = new JDialog(frameGUI, "User input", false);
			moveDialog.setLayout(new BorderLayout());
			JTextPane textPane = new JTextPane();
			textPane.setEditable(false);
			textPane.setText("Please give your move");
			moveDialog.add(BorderLayout.NORTH, textPane);
			moveInputField = new JTextField();
			moveDialog.add(BorderLayout.CENTER, moveInputField);
			moveOK = new JButton("OK");
			moveOK.addActionListener(this);
			moveDialog.add(BorderLayout.EAST, moveOK);
			moveDialog.pack();
			moveDialog.setLocationRelativeTo(frameGUI);
			moveDialog.setVisible(true);
			try {
				moveInputted.await(TUIController.MESSAGE_FREQUENCY, TimeUnit.SECONDS);
			} catch (InterruptedException e) {
				System.err.println("Got interrupted");
			}
			moveDialog.dispose();
			return moveInput;
		} finally {
			moveInputLock.unlock();
		}
	}
	
	public String getAddress() {
		return (String) JOptionPane.showInputDialog(frameGUI, "Please enter the server address:");
	}
	
	public void close() {
		frameGUI.dispose();
	}
}
