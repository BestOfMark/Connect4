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

	private JFrame frameGUI;
	private JTextArea fieldArea;
	private JTextArea internMessages;
	private JTextArea chatMessages;
	private JTextField outwardChat;
	private JButton sendChat;
	private JButton gameStart;
	
	public GUI(Client client) {
		super(client);
		
		//Initialize the GUI frame
		frameGUI = new JFrame("Connect4 GUI");
		frameGUI.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		frameGUI.setResizable(false);
		
		//This JPanel contains the field text area and the internal messages text area.
		JPanel div = new JPanel(new BorderLayout());
		
		//The field is printed on a JTextArea inside a JPanel with a border;
		JPanel p1 = new JPanel();
		p1.setBorder(BorderFactory.createTitledBorder("Field"));
		fieldArea = new JTextArea(10, 80);
		fieldArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
		fieldArea.setEditable(false);
		p1.add(fieldArea);
		div.add(BorderLayout.NORTH, p1);
		
		//The internal messages are written to a scrollable JTextArea inside a bordered JPanel
		JPanel p2 = new JPanel();
		p2.setBorder(BorderFactory.createTitledBorder("Console"));
		internMessages = new JTextArea(10, 50);
		internMessages.setEditable(false);
		internMessages.setLineWrap(true);
		internMessages.setWrapStyleWord(true);
		JScrollPane scroll = new JScrollPane(internMessages, 
				JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		p2.add(scroll);
		div.add(BorderLayout.SOUTH, p2);
		
		//The chat messages are written to a scrollable JTextArea inside a bordered JPanel
		//Also the input field for chat messages and a Send button are inside this JPanel
		JPanel p3 = new JPanel(new BorderLayout());
		p3.setBorder(BorderFactory.createTitledBorder("Chat"));
		chatMessages = new JTextArea(21, 30);
		chatMessages.setEditable(false);
		chatMessages.setLineWrap(true);
		chatMessages.setWrapStyleWord(true);
		JScrollPane scroll2 = new JScrollPane(chatMessages, 
				JScrollPane.VERTICAL_SCROLLBAR_ALWAYS, JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
		outwardChat = new JTextField();
		sendChat = new JButton("Send");
		sendChat.addActionListener(this);
		p3.add(BorderLayout.NORTH, scroll2);
		p3.add(BorderLayout.CENTER, outwardChat);
		p3.add(BorderLayout.EAST, sendChat);

		//A giant button to request a new game
		gameStart = new JButton("New game");
		gameStart.addActionListener(this);
		gameStart.setEnabled(true);
		
		//Add all the components to the frame and set it visible
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

	/**
	 * This is method is fired either by the New Game button, or by the OK button in the 
	 * move-pop-up or by the Send Chat button.
	 */
	@Override
	public void actionPerformed(ActionEvent e) {
		if (e.getSource() == gameStart) {
			//A new game is to be requested
			try {
				control.client.getProtocoller().cmdGameRequest();
				internalMessage("Game request sent");
			} catch (IOException e1) {
				internalMessage("Something went wrong while sending game request");
			}
		} else if (e.getSource() == sendChat) {
			//A chat message is to be send to the server
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

	//Fields used in the pop-up dialog
	private String moveInput;
	private JButton moveOK;
	private JTextField moveInputField;
	private JDialog moveDialog;
	private static ReentrantLock moveInputLock = new ReentrantLock();
	private static Condition moveInputted = moveInputLock.newCondition();
	
	/**
	 * Spawn a pop-up that requests a move from the user. The method blocks until input is 
	 * received from the user or the method times out after the timeout time specified in 
	 * the controller.
	 * @return the move that the player entered, or null if the move timed out.
	 */
	synchronized public String getMove() {
		moveInputLock.lock();
		try {
			moveInput = null;
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
				moveInputted.await(control.timeout, TimeUnit.MILLISECONDS);
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
